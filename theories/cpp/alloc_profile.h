// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// alloc_profile.h -- opt-in global allocation counters for measuring
// Crane-generated code's total heap allocation volume (count + bytes),
// independent of any one type's own instrumentation (e.g. arena.h's
// CRANE_ARENA_PROFILE, which only counts arena bumps and capsule freezes). Compiled in
// only when CRANE_ALLOC_PROFILE is defined; zero overhead otherwise.
//
// Usage: define CRANE_ALLOC_PROFILE, include this header once from the
// program's main translation unit (it overrides the global operator
// new/delete for the whole binary), then read crane::alloc_profile_stats()
// after the region of interest.

#pragma once

#ifdef CRANE_ALLOC_PROFILE

#include <atomic>
#include <cstdio>
#include <cstdlib>
#include <new>

// When also defined, backtrace()-based call-site aggregation is captured
// for a sample of allocations (every Nth, see CRANE_ALLOC_PROFILE_SAMPLE)
// in addition to the always-on size histogram. This is expensive (a stack
// walk + symbolication per sampled allocation) so it is opt-in and
// separate from the cheap size-histogram path.
#ifdef CRANE_ALLOC_PROFILE_BACKTRACE
#include <execinfo.h>
#include <cstring>
#include <mutex>
#include <unordered_map>
#include <vector>
#include <string>
#include <algorithm>
#endif

namespace crane {

// Exact-size buckets for sizes [0, kHistN); one overflow bucket for
// anything >= kHistN.
constexpr std::size_t kHistN = 256;

struct alloc_profile_stats_t {
    std::atomic<unsigned long long> news{0};
    std::atomic<unsigned long long> bytes{0};
    std::atomic<unsigned long long> deletes{0};
    std::atomic<unsigned long long> hist_count[kHistN + 1] = {};
    std::atomic<unsigned long long> hist_bytes[kHistN + 1] = {};
};

inline alloc_profile_stats_t& alloc_profile_stats() noexcept
{
    static alloc_profile_stats_t s;
    return s;
}

#ifdef CRANE_ALLOC_PROFILE_BACKTRACE
struct bt_profile_t {
    std::mutex mu;
    std::unordered_map<std::string, unsigned long long> count;
    std::unordered_map<std::string, unsigned long long> bytes;
};

// Deliberately leaked (never destroyed): this is diagnostic-only code, and
// avoiding destruction sidesteps static-destruction-order issues where the
// mutex could be torn down before the atexit report handler runs (the
// report's own atexit is registered at static-init time, i.e. very early,
// so by LIFO ordering it would otherwise run *after* a function-local
// static's destructor, in this case reading/locking an already-destroyed
// mutex).
inline bt_profile_t& bt_profile() noexcept
{
    static bt_profile_t* p = new bt_profile_t();
    return *p;
}

// Reentrancy guard: backtrace_symbols() itself calls malloc, which would
// otherwise recurse into operator new and deadlock/blow the stack.
inline bool& bt_in_progress() noexcept
{
    static thread_local bool v = false;
    return v;
}

inline void bt_record(std::size_t sz) noexcept
{
    if (bt_in_progress()) return;
    bt_in_progress() = true;
    constexpr int kMaxFrames = 6;
    void* frames[kMaxFrames];
    int n = ::backtrace(frames, kMaxFrames);
    char** syms = ::backtrace_symbols(frames, n);
    if (syms) {
        // Skip frame 0/1 (this function + operator new itself); join a
        // couple of frames above that into one key.
        std::string key;
        for (int i = 2; i < n && i < 5; ++i) {
            if (!key.empty()) key += " <- ";
            key += syms[i];
        }
        {
            std::lock_guard<std::mutex> lk(bt_profile().mu);
            bt_profile().count[key]++;
            bt_profile().bytes[key] += sz;
        }
        std::free(syms);
    }
    bt_in_progress() = false;
}
#endif  // CRANE_ALLOC_PROFILE_BACKTRACE

inline void alloc_profile_report(const char* label) noexcept
{
    auto& s = alloc_profile_stats();
    std::fprintf(
        stderr,
        "[alloc_profile] %s: news=%llu bytes=%llu deletes=%llu\n",
        label,
        s.news.load(std::memory_order_relaxed),
        s.bytes.load(std::memory_order_relaxed),
        s.deletes.load(std::memory_order_relaxed));
    std::fprintf(stderr, "[alloc_profile] size histogram (size: count, total_bytes):\n");
    for (std::size_t i = 0; i <= kHistN; ++i) {
        auto c = s.hist_count[i].load(std::memory_order_relaxed);
        if (c == 0) continue;
        auto b = s.hist_bytes[i].load(std::memory_order_relaxed);
        if (i == kHistN) {
            std::fprintf(stderr, "  >=%zu: %llu, %llu\n", kHistN, c, b);
        } else {
            std::fprintf(stderr, "  %zu: %llu, %llu\n", i, c, b);
        }
    }
#ifdef CRANE_ALLOC_PROFILE_BACKTRACE
    {
        // Reuse the bt_record reentrancy guard for this whole critical
        // section: building/sorting the vector below allocates via the
        // overridden operator new, and if that allocation happened to be
        // sampled, bt_record() would try to re-lock bt_profile().mu while
        // we already hold it here (self-deadlock on a non-recursive
        // mutex). Setting the guard first makes any such nested
        // allocation skip bt_record() entirely, same as real recursion
        // into bt_record() itself.
        bt_in_progress() = true;
        std::lock_guard<std::mutex> lk(bt_profile().mu);
        std::fprintf(stderr, "[alloc_profile] sampled call sites (%zu distinct):\n",
                     bt_profile().count.size());
        std::vector<std::pair<std::string, unsigned long long>> v(
            bt_profile().bytes.begin(), bt_profile().bytes.end());
        std::sort(v.begin(), v.end(), [](auto& a, auto& b) { return a.second > b.second; });
        std::size_t shown = 0;
        for (auto& kv : v) {
            if (shown++ >= 40) break;
            std::fprintf(stderr, "  bytes=%llu count=%llu :: %s\n",
                         kv.second, bt_profile().count[kv.first], kv.first.c_str());
        }
        bt_in_progress() = false;
    }
#endif
}

namespace detail {
inline int install_alloc_profile_atexit() noexcept
{
    std::atexit([] { alloc_profile_report("atexit"); });
    return 0;
}
inline int alloc_profile_atexit_installed = install_alloc_profile_atexit();
}  // namespace detail

}  // namespace crane

void* operator new(std::size_t sz)
{
    auto& s = crane::alloc_profile_stats();
    s.news.fetch_add(1, std::memory_order_relaxed);
    s.bytes.fetch_add(sz, std::memory_order_relaxed);
    std::size_t bucket = sz < crane::kHistN ? sz : crane::kHistN;
    s.hist_count[bucket].fetch_add(1, std::memory_order_relaxed);
    s.hist_bytes[bucket].fetch_add(sz, std::memory_order_relaxed);
#ifdef CRANE_ALLOC_PROFILE_BACKTRACE
    // Sample every Nth allocation to keep overhead tractable.
    static std::atomic<unsigned long long> ctr{0};
    if (ctr.fetch_add(1, std::memory_order_relaxed) % 500 == 0) {
        crane::bt_record(sz);
    }
#endif
    void* p = std::malloc(sz == 0 ? 1 : sz);
    if (!p) throw std::bad_alloc();
    return p;
}

void operator delete(void* p) noexcept
{
    crane::alloc_profile_stats().deletes.fetch_add(1, std::memory_order_relaxed);
    std::free(p);
}

void operator delete(void* p, std::size_t) noexcept
{
    crane::alloc_profile_stats().deletes.fetch_add(1, std::memory_order_relaxed);
    std::free(p);
}

#endif  // CRANE_ALLOC_PROFILE
