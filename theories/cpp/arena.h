// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// arena.h — region ("arena") allocation for Crane-extracted recursive inductives.
//
// Memory model (scope-owns-arena):
//   Arena-ness is a property of a *region*, decided at run time, not a property
//   of a type.  Layout never changes: a recursive field is the same smart-pointer
//   handle it is in a non-arena build, and every call site is byte-identical.
//   What the `Crane Arena` master switch changes is only which factory the
//   recursive-field constructor calls.  Whether that factory bump-allocates
//   depends on whether a `crane::arena_scope` is installed on the current thread
//   when it runs; with no scope, allocation goes to the heap as usual.
//
//   An earlier design keyed arenas to *types* (`Crane Arena t` made t's recursive
//   fields raw pointers into an owned region).  That forced deep copies, forbade
//   escape, infected every reachable type, and made arena and non-arena code
//   non-interoperable because the layout differed.  It is gone.
//
// Safety:
//   - Values may escape their scope.  An escaping node holds a refcounted
//     *keeper* for the region (see `acquire_arena_keeper` below), so the region
//     outlives the scope exactly as long as something still points into it.  The
//     pathological case is a delayed free, not a dangling pointer.
//   - `std::pmr::monotonic_buffer_resource` never runs element destructors, so a
//     node whose payload is *not* trivially destructible (e.g. holds a
//     std::string or another value type) would leak.  We prevent that with a
//     zero-heap destructor registry: trivially-destructible nodes cost pure
//     bump-allocation; only non-trivial nodes register a (ptr, dtor-fn) pair,
//     run in reverse on arena drop.  Memory stays leak-free either way.
//
// Threading:
//   The active arena and its keeper are thread-local: a scope installed on one
//   thread does not affect allocation on another.  A single `crane::arena` is
//   not itself thread-safe, which matches Crane's clone-at-boundary concurrency
//   model.  Not thread-safe by design.

#pragma once

#include <atomic>
#include <cstddef>
#include <cstdio>
#include <memory>
#include <memory_resource>
#include <new>
#include <type_traits>
#include <utility>
#include <vector>

namespace crane {

// A bump-allocated region owning all nodes of one arena-mode inductive value.
class arena {
public:
    arena()
    : res_(std::make_unique<std::pmr::monotonic_buffer_resource>())
    {
    }

    // Move transfers ownership of the region and the node pointers into it stay
    // valid (they point into heap blocks the resource owns, kept alive by res_).
    arena(arena&&) noexcept            = default;
    arena& operator=(arena&&) noexcept = default;

    // Regions are not copyable.  Copying an extracted value never reaches here:
    // handles alias in O(1) whether or not the pointee is arena-backed.
    arena(const arena&)            = delete;
    arena& operator=(const arena&) = delete;

    ~arena()
    {
        // Run node destructors (only non-trivial ones were registered), newest
        // first, then res_'s destructor frees every buffer in one shot.
        for (auto it = dtors_.rbegin(); it != dtors_.rend(); ++it) {
            it->second(it->first);
        }
    }

    // Allocate and construct a T inside the region; returns a raw pointer that
    // lives as long as this arena.
    template <typename T, typename... Args>
    T* alloc(Args&&... args)
    {
        void* mem = res_->allocate(sizeof(T), alignof(T));
        T*    p   = ::new (mem) T(std::forward<Args>(args)...);
        if constexpr (!std::is_trivially_destructible_v<T>) {
            dtors_.emplace_back(
                static_cast<void*>(p),
                [](void* q) { static_cast<T*>(q)->~T(); });
        }
        return p;
    }

    // Raw resource, e.g. to construct pmr containers that allocate in-region.
    std::pmr::memory_resource* resource() noexcept { return res_.get(); }

private:
    // unique_ptr keeps the resource object address-stable across handle moves
    // (monotonic_buffer_resource is itself neither copyable nor movable).
    std::unique_ptr<std::pmr::monotonic_buffer_resource>  res_;
    std::vector<std::pair<void*, void (*)(void*)>>        dtors_;
};

// -- Ambient arena -----------------------------------------------------------
// Rather than thread an arena through every allocating function's signature,
// allocation sites consult the current thread's ambient arena, whose lifetime is
// bounded by an [arena_scope] RAII guard the caller installs around a build.
// This is what makes region membership dynamic, and hence layout-invariant: the
// same generated code allocates from a region or from the heap depending only on
// whether a scope is open.  Escape is permitted; see [acquire_arena_keeper].

inline arena*& current_arena_ptr() noexcept
{
    static thread_local arena* p = nullptr;
    return p;
}

// Process-wide flag: has any [arena_scope] / [arena_use_scope] ever been
// installed on *any* thread yet?  Distinguishes two very different reasons the
// fallback can be reached:
//   - before the first scope is ever installed anywhere, e.g. a dynamically-
//     initialized global (a memoized regex/DFA table built by a
//     `__cxx_global_var_init`/static constructor that runs before `main`, on
//     the thread that will later install scopes for real work). This is a
//     normal, expected, one-time program-lifetime allocation.
//   - after scopes are already in routine use elsewhere in the process, some
//     other thread (or a code path on this thread) reaches the fallback with
//     no scope active. That is far more likely a forgotten [arena_scope] on
//     an ephemeral-lifetime build, which is the case worth flagging.
inline std::atomic<bool>& any_scope_ever_installed() noexcept
{
    static std::atomic<bool> installed{false};
    return installed;
}

// Per-thread fallback region, used when no [arena_scope] is active (e.g. a value
// constructed during static initialization, or a caller that never installed a
// scope).  It is never reset during the thread's life, so anything allocated
// here lives until thread exit — correct for program-lifetime values, but it
// does NOT reclaim ephemeral garbage.  Prefer an explicit [arena_scope] to bound
// lifetimes; the fallback only guarantees allocation never dereferences null.
inline arena& fallback_arena()
{
    static thread_local arena g;
#ifndef NDEBUG
    // Debug builds only: warn once per thread the first time the fallback is
    // actually reached *after* some scope has already been installed somewhere
    // in the process, so an embedding that forgot to install an [arena_scope]
    // (and would therefore grow this never-resetting region unboundedly) at
    // least gets a signal in development. Fallback hits that happen before any
    // scope has ever been installed (typically a dynamically-initialized
    // global building a program-lifetime table, e.g. a memoized regex tree,
    // before `main` runs) are expected and do not warn — see
    // [any_scope_ever_installed] above. Release builds compile this away
    // entirely, so the fallback stays zero-overhead there.
    static thread_local bool warned = false;
    if (!warned && any_scope_ever_installed().load(std::memory_order_relaxed)) {
        warned = true;
        std::fprintf(
            stderr,
            "crane::arena: warning: allocating in the never-resetting fallback "
            "arena (no crane::arena_scope / crane::arena_use_scope is active on "
            "this thread). This is correct for program-lifetime values but "
            "leaks ephemeral garbage; install a scope to bound the lifetime.\n");
    }
#endif
    return g;
}

inline arena& current_arena() noexcept
{
    arena* p = current_arena_ptr();
    return p ? *p : fallback_arena();
}

// Allocate a node of type T in the current ambient arena.
template <typename T, typename... Args>
T* arena_alloc(Args&&... args)
{
    return current_arena().alloc<T>(std::forward<Args>(args)...);
}

// -- Runtime scoped-arena allocation ------------------------------------
// The redesign (scoped-arena, 2026-08-10): whether a recursive node is
// bump-allocated from an arena is a *runtime* property of whether a scope is
// currently open, not a compile-time property of the node's type.  A recursive
// field is always the ordinary smart pointer (std::shared_ptr / crane::rc); the
// factory (crane::arena_make_shared / crane::rc<T>::make) checks at the call
// site whether a scope is open and, if so, bump-allocates the node and attaches
// a keeper that keeps the region alive as long as the node is referenced.

// True iff an [arena_scope] or [arena_use_scope] is currently installed on this
// thread (thin, readable wrapper around the ambient-pointer check).
inline bool in_arena_scope() noexcept
{
    return current_arena_ptr() != nullptr;
}

// Per-thread count of nodes that were actually bump-allocated from an arena (as
// opposed to the plain heap fallback).  Always on and near-free; useful as a
// direct, allocator-agnostic observable that a value really is arena-backed
// (see tests/regression/arena_scoping).  Incremented by [arena_make_shared] and
// [crane::rc<T>::make] whenever they take the arena path.
inline unsigned long long& arena_bump_count() noexcept
{
    static thread_local unsigned long long n = 0;
    return n;
}

// A refcounted keeper for the arena an *owning* [arena_scope] installed.  The
// scope publishes a pointer to its own [shared_ptr<arena>] here so an escaping
// node can grab a copy: as long as any node holds a keeper copy the region
// outlives the scope.  A caller-owned [arena_use_scope] publishes nullptr (the
// caller controls the region's lifetime, so escaping nodes get no keeper).
inline std::shared_ptr<arena>*& current_arena_keeper_slot() noexcept
{
    static thread_local std::shared_ptr<arena>* slot = nullptr;
    return slot;
}

// Obtain a keeper for the currently-open scope's arena, or a null handle when
// the current scope is caller-owned ([arena_use_scope]) or there is no scope.
inline std::shared_ptr<arena> acquire_arena_keeper()
{
    std::shared_ptr<arena>* slot = current_arena_keeper_slot();
    return slot != nullptr ? *slot : std::shared_ptr<arena>{};
}

// Arena-aware replacement for [std::make_shared<T>] used by generated factories
// for recursive fields.  When no scope is open this is exactly
// [std::make_shared<T>].  When a scope is open the node's payload is
// bump-allocated from the current arena and returned in a [std::shared_ptr]
// whose deleter runs only the node's destructor (never [delete]: the region owns
// the memory) and captures a keeper so the region cannot be freed while the node
// is still referenced.  Copying such a shared_ptr is an O(1) refcount bump, so
// no deep-copy/clone is ever needed (this is what removes the composite-hang
// failure mode of the old per-type arena representation).
template <typename T, typename... Args>
std::shared_ptr<T> arena_make_shared(Args&&... args)
{
    arena* ap = current_arena_ptr();
    if (ap == nullptr) {
        return std::make_shared<T>(std::forward<Args>(args)...);
    }
    // A scope is open.  Grab the keeper (null under a caller-owned scope) before
    // allocating, then bump-allocate the payload from the region.
    std::shared_ptr<arena> keeper = acquire_arena_keeper();
    void* mem = ap->resource()->allocate(sizeof(T), alignof(T));
    T*    p   = ::new (mem) T(std::forward<Args>(args)...);
    ++arena_bump_count();
    // The deleter never frees [p] (the region owns it); it runs [T]'s destructor
    // so the node's own fields (child smart pointers, etc.) are released, then
    // drops its captured [keeper], releasing this node's claim on the region.
    return std::shared_ptr<T>(p, [keeper](T* q) noexcept { q->~T(); });
}

// -- Shared arena capsules ----------------------------------------------
// Phase 1 (runtime-only, no codegen/Coq surface yet) of the shared-arena-
// capsule design (see ~/crane/docs/shared-arena-capsule-plan.md). A
// `crane::arena` is single-owner: dropping it frees everything in one shot,
// which is exactly wrong for a value that gets stored into a long-lived
// structure (a memo table) and aliased from many places over time — every
// such store would otherwise have to deep-copy the whole value into the
// destination's own arena. `shared_arena` instead lets the *arena itself* be
// referenced-counted: `freeze()` moves an existing (unshared, already-built)
// arena into a refcounted capsule in O(1) (no allocation is copied); copying
// the resulting handle is an O(1) refcount bump regardless of how much is
// allocated inside. A `capsule<T>` pairs a `shared_arena` handle with a raw
// pointer to the value's root node inside it, mirroring how `crane::rc<T>` is
// a (control-block*, T*) pair for the non-arena representation.
#ifdef CRANE_ARENA_PROFILE
// Counts capsules ever created (`freezes`) vs. currently referenced by at
// least one live `capsule<T>`/`shared_arena` handle tree (`live`, best-effort:
// incremented on freeze, this phase does not yet decrement on last-handle
// drop -- that needs a dtor hook on shared_arena, deferred until a real
// consumer of capsule<T> exists to exercise it).
struct capsule_stats_t {
    std::atomic<unsigned long long> freezes{0};
    std::atomic<unsigned long long> live{0};
};
inline capsule_stats_t& capsule_stats() noexcept
{
    static capsule_stats_t s;
    return s;
}
#endif

class shared_arena {
public:
    // Move an existing single-owner arena into a fresh, refcounted capsule.
    // O(1): transfers the pmr resource's ownership, copies nothing.
    static shared_arena freeze(arena&& a)
    {
#ifdef CRANE_ARENA_PROFILE
        capsule_stats().freezes.fetch_add(1, std::memory_order_relaxed);
        capsule_stats().live.fetch_add(1, std::memory_order_relaxed);
#endif
        return shared_arena(std::make_shared<arena>(std::move(a)));
    }

    shared_arena(const shared_arena&)            = default;
    shared_arena(shared_arena&&) noexcept        = default;
    shared_arena& operator=(const shared_arena&) = default;
    shared_arena& operator=(shared_arena&&) noexcept = default;

    arena& get() const noexcept { return *impl_; }

    // Null handle: only for default-constructing a [capsule<T>] field before
    // it's ever assigned (e.g. a variant's synthesized default constructor
    // picking an unrelated alternative). Dereferencing [get()] on a null
    // handle is undefined, same contract as a null [shared_ptr].
    shared_arena() noexcept = default;

private:
    explicit shared_arena(std::shared_ptr<arena> impl) : impl_(std::move(impl)) {}

    std::shared_ptr<arena> impl_;
};

// A value whose root lives inside a `shared_arena`. Copying a `capsule<T>` is
// an O(1) refcount bump on the underlying arena (via `shared_arena`'s
// `shared_ptr`), regardless of the size of the tree rooted at `root`. This is
// the operation a store-many/read-many structure (e.g. an AVL map's rebalance
// path) needs and a plain arena-mode value (clone-at-boundary) doesn't have.
template <typename T>
class capsule {
public:
    capsule() noexcept : root_(nullptr) {}
    capsule(shared_arena owner, T* root) noexcept : owner_(std::move(owner)), root_(root) {}

    T&       operator*() const noexcept { return *root_; }
    T*       operator->() const noexcept { return root_; }
    T*       get() const noexcept { return root_; }
    shared_arena owner() const noexcept { return owner_; }

private:
    shared_arena owner_;
    T*           root_;
};

}  // namespace crane

// Overload of [crane_raw] (declared in crane_fn.h for std::shared_ptr<T> / T*,
// and in rc.h for crane::rc<T>) for [crane::capsule<T>]: extract the raw
// pointer. Kept here so it is available whenever capsule<T> is in use (with or
// without crane_fn.h included), so loopify's raw-pointer extraction works
// uniformly across pointer flavors -- needed because `Crane Arena Shared`
// fields are [crane::capsule<T>], not a bare [T*] or [shared_ptr<T>].
template <typename T> T *crane_raw(const crane::capsule<T> &p) noexcept {
  return p.get();
}

namespace crane {

// Build a value of type T inside a fresh, single-owner arena via `build`
// (which must return the root T*, allocating via `arena_alloc<T>` under an
// `arena_use_scope` for `a` -- the caller sets that up), then freeze that
// arena into a capsule in O(1). Convenience wrapper for the common
// "construct once, then store/share" pattern.
template <typename T, typename F>
capsule<T> freeze_into(arena&& a, F&& build)
{
    T* root = build(a);
    return capsule<T>(shared_arena::freeze(std::move(a)), root);
}

// -- Codegen entry point for `Crane Arena Shared` -----------------------
// Generated code for an arena-shared inductive allocates every node of that
// type into ONE thread-local shared capsule per type `T` (lazily created,
// frozen immediately, never explicitly reset -- same accepted tradeoff as
// `fallback_arena()`: no reclamation, but a lex/parse run's regex-shaped
// working set is bounded, and the point of this feature is exactly that
// such values are long-lived and widely aliased for the run's duration
// anyway). Because every value of type `T` lives in the same capsule, a
// generated deep-copy constructor for `T` never needs to clone across
// nodes of `T` -- copying a `capsule<T>` field is already an O(1) refcount
// bump, which is the whole point: it turns the "clone on every AVL-
// rebalance-triggered store" cost that made plain `Crane Arena` pathological
// for table-stored values (see docs/shared-arena-capsule-plan.md) into a
// no-op-cost aliasing operation, at the price of never reclaiming individual
// nodes until every capsule<T> handle across the whole thread drops (whole-
// type granularity, not whole-program: unrelated arena-shared types get
// their own independent capsule and lifetime).
template <typename T>
shared_arena& shared_capsule_for() noexcept
{
    static thread_local shared_arena a = shared_arena::freeze(arena{});
    return a;
}

template <typename T, typename... Args>
capsule<T> arena_shared_alloc(Args&&... args)
{
    shared_arena& cap = shared_capsule_for<T>();
    T*            p   = cap.get().alloc<T>(std::forward<Args>(args)...);
    return capsule<T>(cap, p);
}

// RAII: install a fresh arena as the current one for the duration of this scope
// (restoring any previous one on exit, so scopes nest).
class arena_scope {
public:
    // The scope owns its region through a refcounted [shared_ptr<arena>] from
    // the start (rather than freezing-on-escape a bare [arena] member): a node
    // that escapes the scope simply keeps a copy of this keeper alive, so the
    // region is destroyed exactly when the scope AND every escaped node are
    // gone.  If nothing escapes, [keeper_] is the sole owner and the region is
    // freed in O(1) when this object is destroyed.  This is strictly simpler
    // than a move-out-on-first-escape scheme and has no moved-from-arena hazard.
    arena_scope()
    : keeper_(std::make_shared<arena>())
    , prev_(current_arena_ptr())
    , prev_keeper_(current_arena_keeper_slot())
    {
        current_arena_ptr() = keeper_.get();
        current_arena_keeper_slot() = &keeper_;
        any_scope_ever_installed().store(true, std::memory_order_relaxed);
    }
    ~arena_scope()
    {
        current_arena_ptr() = prev_;
        current_arena_keeper_slot() = prev_keeper_;
        // keeper_ drops here; the region is freed now unless a node escaped.
    }

    arena_scope(const arena_scope&)            = delete;
    arena_scope& operator=(const arena_scope&) = delete;

    arena& get() noexcept { return *keeper_; }

private:
    std::shared_ptr<arena>  keeper_;
    arena*                  prev_;
    std::shared_ptr<arena>* prev_keeper_;
};

// RAII: install a *caller-supplied* arena as the current one for the duration
// of this scope (restoring any previous one on exit, so scopes nest).  Unlike
// [arena_scope], this owns nothing: the caller controls the arena's lifetime,
// which lets one arena be reused across several sequential top-level calls
// (amortizing allocation) or be pre-sized/pre-warmed before the calls.
class arena_use_scope {
public:
    explicit arena_use_scope(arena& a)
    : prev_(current_arena_ptr())
    , prev_keeper_(current_arena_keeper_slot())
    {
        current_arena_ptr() = &a;
        // Caller-owned region: no refcounted keeper is published, so escaping
        // nodes get a null keeper and the caller alone controls the lifetime.
        current_arena_keeper_slot() = nullptr;
        any_scope_ever_installed().store(true, std::memory_order_relaxed);
    }
    ~arena_use_scope()
    {
        current_arena_ptr() = prev_;
        current_arena_keeper_slot() = prev_keeper_;
    }

    arena_use_scope(const arena_use_scope&)            = delete;
    arena_use_scope& operator=(const arena_use_scope&) = delete;

private:
    arena*                  prev_;
    std::shared_ptr<arena>* prev_keeper_;
};

}  // namespace crane
