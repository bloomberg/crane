// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// count_rc.h -- opt-in reference-count traffic counters.
//
// Measurement scaffolding for borrow inference: it answers "how many
// reference-count operations does this program actually perform, and how many
// of them could a borrow have avoided".  Selected by extracting with
// CRANE_COUNT_RC=1 set in the environment, which makes Crane spell every
// shared pointer `crane::counting_ptr` instead of `std::shared_ptr`.  It is
// measurement-only and never appears in ordinary output.
//
// `counting_ptr<T>` is a `std::shared_ptr<T>` that tallies the operations that
// touch the control block:
//
//   dups  -- a copy of a non-null pointer: one atomic increment.
//   drops -- a non-null pointer losing its referent (destruction, or
//            assignment over it): one atomic decrement.
//   frees -- a drop that took the count to zero, so the object died.
//
// A dup/drop pair that a borrow would remove is exactly what the pass is
// trying to eliminate, so `dups` is the headline number.  `frees` separates
// the traffic that is doing real work (the last drop, which must happen
// however the program is compiled) from the traffic that is pure overhead.
//
// The counters are per-thread and summed on thread exit, so a threaded program
// reports its whole total without any contention while it runs.
//
// The report goes to stderr at exit, or to the file named by CRANE_RC_LOG.
//
// Compile with -DCRANE_COUNT_RC_SITES to additionally attribute dups to the
// code that performs them: every Nth dup (CRANE_RC_SAMPLE, default 1024)
// records its return address, and the report lists the hottest, named via
// `dladdr`.  Pipe the report through `c++filt` to read the names.  This
// answers "which generated function is doing the copying", which is the
// question that decides where borrow inference pays.

#ifndef CRANE_COUNT_RC_H
#define CRANE_COUNT_RC_H

#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <utility>

#if defined(__GLIBC__)
#include <errno.h>  // program_invocation_short_name
#endif

#ifdef CRANE_COUNT_RC_SITES
#include <dlfcn.h>  // dladdr, for naming a sampled dup site
#endif

namespace crane {

struct rc_counters {
    std::uint64_t dups = 0;
    std::uint64_t drops = 0;
    std::uint64_t frees = 0;
};

namespace detail {

inline std::atomic<std::uint64_t>& rc_total_dups() noexcept
{
    static std::atomic<std::uint64_t> v{0};
    return v;
}

inline std::atomic<std::uint64_t>& rc_total_drops() noexcept
{
    static std::atomic<std::uint64_t> v{0};
    return v;
}

inline std::atomic<std::uint64_t>& rc_total_frees() noexcept
{
    static std::atomic<std::uint64_t> v{0};
    return v;
}

// Per-thread tallies, folded into the atomic totals when the thread ends.
// Counting in a thread_local and publishing once keeps the measurement from
// changing what it measures: an atomic increment per dup would cost about as
// much as the dup.
struct rc_thread_counters {
    rc_counters c;

    ~rc_thread_counters()
    {
        rc_total_dups().fetch_add(c.dups, std::memory_order_relaxed);
        rc_total_drops().fetch_add(c.drops, std::memory_order_relaxed);
        rc_total_frees().fetch_add(c.frees, std::memory_order_relaxed);
        // Published; zero so that a report running after this destructor
        // (static and thread-local destruction interleave at exit) counts
        // these once, from the totals, rather than twice or not at all.
        c = rc_counters{};
    }
};

inline rc_counters& rc_local() noexcept
{
    static thread_local rc_thread_counters t;
    return t.c;
}

#ifdef CRANE_COUNT_RC_SITES
// Sampled dup sites: return address -> how many sampled dups came from it.
//
// Process-wide rather than per-thread, and therefore atomic.  A thread-local
// table would be cheaper, but it shares the lifetime problem the counters have
// -- thread-local and static destruction interleave at exit, so a table read
// from the exit-time report may be one the runtime has already torn down and
// rebuilt empty.  Only one in CRANE_RC_SAMPLE dups reaches this table, so the
// synchronization is paid a fraction of a percent of the time.
struct rc_sites {
    static constexpr std::size_t kSlots = 4096;
    std::atomic<const void*> addr[kSlots] = {};
    std::atomic<std::uint64_t> hits[kSlots] = {};

    void record(const void* pc) noexcept
    {
        // Open addressing, no eviction: a table this size holds far more
        // distinct call sites than generated code has, and refusing to evict
        // keeps a hot site from being displaced by a cold one.
        const std::size_t h = (reinterpret_cast<std::uintptr_t>(pc) >> 4) % kSlots;
        for (std::size_t i = 0; i < kSlots; ++i) {
            const std::size_t j = (h + i) % kSlots;
            const void* cur = addr[j].load(std::memory_order_relaxed);
            if (cur == nullptr)
                // On a lost race the exchange leaves the winner in `cur`, so
                // the test below still decides this slot correctly.
                addr[j].compare_exchange_strong(cur, pc, std::memory_order_relaxed);
            if (cur == nullptr || cur == pc) {
                hits[j].fetch_add(1, std::memory_order_relaxed);
                return;
            }
        }
    }
};

inline rc_sites& rc_site_table() noexcept
{
    static rc_sites t;
    return t;
}

// How many dups this thread has seen, for the 1-in-N decision.  This one may
// safely be thread-local and may safely be reset at thread exit: it only paces
// the sampling, and nothing is read back from it.
inline std::uint64_t& rc_seen() noexcept
{
    static thread_local std::uint64_t n = 0;
    return n;
}

inline std::uint64_t rc_sample_period() noexcept
{
    static const std::uint64_t n = [] {
        const char* e = std::getenv("CRANE_RC_SAMPLE");
        const long v = e ? std::strtol(e, nullptr, 10) : 0;
        return v > 0 ? static_cast<std::uint64_t>(v) : 1024;
    }();
    return n;
}

inline void rc_sample_site(const void* pc) noexcept
{
    if (++rc_seen() % rc_sample_period() != 0) return;
    rc_site_table().record(pc);
}
#endif  // CRANE_COUNT_RC_SITES

}  // namespace detail

// The totals so far, including the calling thread's unpublished tally.  Safe
// to call at any point; exact only once the other threads have joined.
inline rc_counters rc_stats() noexcept
{
    rc_counters r = detail::rc_local();
    r.dups += detail::rc_total_dups().load(std::memory_order_relaxed);
    r.drops += detail::rc_total_drops().load(std::memory_order_relaxed);
    r.frees += detail::rc_total_frees().load(std::memory_order_relaxed);
    return r;
}

// The running program's own name, so that a sweep appending every test's
// counters to one CRANE_RC_LOG can tell them apart without the harness having
// to pass anything in.
inline const char* rc_program_name() noexcept
{
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__)
    const char* n = getprogname();
    return n ? n : "program";
#elif defined(__GLIBC__)
    return program_invocation_short_name ? program_invocation_short_name
                                         : "program";
#else
    return "program";
#endif
}

inline void rc_report(const char* label) noexcept
{
    const rc_counters s = rc_stats();
    const char* path = std::getenv("CRANE_RC_LOG");
    std::FILE* out = path ? std::fopen(path, "a") : stderr;
    if (!out) out = stderr;
    std::fprintf(out, "[count_rc] %s: dups=%llu drops=%llu frees=%llu\n", label,
                 static_cast<unsigned long long>(s.dups),
                 static_cast<unsigned long long>(s.drops),
                 static_cast<unsigned long long>(s.frees));
#ifdef CRANE_COUNT_RC_SITES
    {
        detail::rc_sites& t = detail::rc_site_table();
        std::fprintf(out, "[count_rc] %s: sampled dup sites (1 in %llu)\n",
                     label,
                     static_cast<unsigned long long>(detail::rc_sample_period()));
        for (std::size_t i = 0; i < detail::rc_sites::kSlots; ++i) {
            const void* pc = t.addr[i].load(std::memory_order_relaxed);
            if (!pc) continue;
            Dl_info info;
            const bool named =
                dladdr(pc, &info) != 0 && info.dli_sname != nullptr;
            std::fprintf(out, "  %llu %p %s\n",
                         static_cast<unsigned long long>(
                             t.hits[i].load(std::memory_order_relaxed)),
                         pc, named ? info.dli_sname : "?");
        }
    }
#endif
    if (out != stderr) std::fclose(out);
}

namespace detail {

// Reports once, at exit, without the program having to call anything.
struct rc_reporter {
    ~rc_reporter() { rc_report(rc_program_name()); }
};

inline rc_reporter rc_reporter_instance;

}  // namespace detail

/// A `std::shared_ptr` that counts the operations touching its control block.
///
/// Derivation rather than composition, so that every `shared_ptr` member
/// Crane's output uses -- `operator*`, `get`, `use_count`, `operator bool`,
/// the owner-based comparisons -- is inherited unchanged and this file stays
/// short.  Nothing ever deletes through the base, so the absent virtual
/// destructor is not a hazard; nothing stores one of these where a
/// `std::shared_ptr` is expected either, because Crane spells *every* shared
/// pointer the same way.
template <class T>
class counting_ptr : public std::shared_ptr<T> {
    using base = std::shared_ptr<T>;

    void count_dup() noexcept
    {
        if (this->get() == nullptr) return;
        ++detail::rc_local().dups;
#ifdef CRANE_COUNT_RC_SITES
        detail::rc_sample_site(__builtin_return_address(0));
#endif
    }

    // Call *before* the referent is released, so that `use_count` still
    // reports whether this is the last owner.
    void count_drop() noexcept
    {
        if (this->get() == nullptr) return;
        ++detail::rc_local().drops;
        if (this->use_count() == 1) ++detail::rc_local().frees;
    }

  public:
    constexpr counting_ptr() noexcept = default;
    constexpr counting_ptr(std::nullptr_t) noexcept {}

    // Adopting an already-built `std::shared_ptr` (what `make_counting` and
    // `shared_from_this` hand back) transfers ownership: no dup.
    counting_ptr(base p) noexcept : base(std::move(p)) {}

    counting_ptr(const counting_ptr& o) : base(o) { count_dup(); }
    counting_ptr(counting_ptr&& o) noexcept : base(std::move(o)) {}

    template <class U, class = std::enable_if_t<std::is_convertible_v<U*, T*>>>
    counting_ptr(const counting_ptr<U>& o) : base(o)
    {
        count_dup();
    }

    template <class U, class = std::enable_if_t<std::is_convertible_v<U*, T*>>>
    counting_ptr(counting_ptr<U>&& o) noexcept : base(std::move(o))
    {
    }

    counting_ptr& operator=(const counting_ptr& o)
    {
        if (this != &o) {
            count_drop();
            base::operator=(o);
            count_dup();
        }
        return *this;
    }

    counting_ptr& operator=(counting_ptr&& o) noexcept
    {
        if (this != &o) {
            count_drop();
            base::operator=(std::move(o));
        }
        return *this;
    }

    counting_ptr& operator=(std::nullptr_t) noexcept
    {
        count_drop();
        base::operator=(nullptr);
        return *this;
    }

    void reset() noexcept
    {
        count_drop();
        base::reset();
    }

    ~counting_ptr() { count_drop(); }
};

template <class T, class... Args>
counting_ptr<T> make_counting(Args&&... args)
{
    return counting_ptr<T>(std::make_shared<T>(std::forward<Args>(args)...));
}

}  // namespace crane

#endif  // CRANE_COUNT_RC_H
