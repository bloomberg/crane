// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// arena.h — region ("arena") allocation for Crane-extracted recursive inductives.
//
// Memory model (handle-owns-arena):
//   A recursive inductive extracted in arena mode is a *handle* value that owns a
//   `crane::arena`.  Its recursive fields are raw pointers into that arena.  The
//   whole value is destroyed in O(1) by dropping the arena (one bulk free), with
//   no per-node `free` and no reference counting.
//
// Safety:
//   - Nodes are only reachable through the owning handle, so a raw node pointer
//     cannot outlive its arena (lifetime bugs are hard to express).
//   - `std::pmr::monotonic_buffer_resource` never runs element destructors, so a
//     node whose payload is *not* trivially destructible (e.g. holds a
//     std::string or another value type) would leak.  We prevent that with a
//     zero-heap destructor registry: trivially-destructible nodes cost pure
//     bump-allocation; only non-trivial nodes register a (ptr, dtor-fn) pair,
//     run in reverse on arena drop.  Memory stays leak-free either way.
//
// Threading:
//   A `crane::arena` has a single owner (its handle).  It is not shared across
//   threads; this matches Crane's clone-at-boundary concurrency model.  Not
//   thread-safe by design.

#pragma once

#include <atomic>
#include <cstddef>
#include <cstdio>
#include <memory>
#include <memory_resource>
#include <new>
#include <type_traits>
#include <unordered_map>
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

    // Regions are not copyable: value-copying an arena-mode handle deep-copies
    // its node graph into a *fresh* arena at the handle level, not here.
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
// First-slice threading strategy: instead of passing an arena through every
// allocating function's signature, allocation sites use the current thread's
// ambient arena, whose lifetime is bounded by an [arena_scope] RAII guard the
// caller installs around a build.  Not a general solution (a value must not
// outlive the scope that built it) but the minimal delta to a working,
// benchmarkable arena representation; explicit-parameter / handle-owned models
// are the follow-up for the general safe API.

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

// -- Sharing-preserving deep copy ---------------------------------------
// Generated arena-mode copy constructors (Crane Arena) recursively clone
// every reachable node, because raw pointers carry no refcount to bump. A
// naive per-field `arena_alloc<T>(*src)` clones each *reference* to a node,
// not each node: if the source value is a DAG (the same node pointer reached
// through more than one field/parent — e.g. a hash-consed/interned value,
// see Crane Intern), every additional reference re-clones the whole subtree
// hanging off it. That turns one O(size-of-DAG) copy into something
// exponential in the DAG's sharing depth. `arena_clone<T>` fixes this by
// memoizing on source-pointer identity for the duration of one top-level
// copy: the first time a given source node is seen it is cloned (invoking
// its own copy constructor, which recurses into `arena_clone` again for its
// own pointer fields); every subsequent reference to that same source
// pointer within the same top-level copy reuses the already-cloned target,
// restoring the source's sharing structure in the copy.
//
// The memo is thread-local and cleared automatically between unrelated
// top-level copies (tracked via a call-depth counter): only the outermost
// `arena_clone` invocation in a given call chain clears it, so nested
// recursive clones (reached while that outermost call is still on the
// stack) share one memo, and the memo never leaks entries across unrelated
// copies, which matters since a `const void*` source address is not a
// stable identity of node *content* — it silently keys the wrong node if
// left stale.
inline std::unordered_map<const void*, void*>& arena_clone_memo() noexcept
{
    static thread_local std::unordered_map<const void*, void*> m;
    return m;
}

inline int& arena_clone_depth() noexcept
{
    static thread_local int d = 0;
    return d;
}

// -- Debug instrumentation: quantify clone volume ---------------------------
// Counts, per-process, how many times arena_clone actually allocates (a
// memo miss -- a genuine new node copy) vs. how many times it's called at
// all (misses + memo hits). Compiled in only under CRANE_ARENA_PROFILE, so
// it costs nothing in normal builds. Read via arena_clone_stats().
#ifdef CRANE_ARENA_PROFILE
struct arena_clone_stats_t {
    std::atomic<unsigned long long> calls{0};
    std::atomic<unsigned long long> misses{0};
};
inline arena_clone_stats_t& arena_clone_stats() noexcept
{
    static arena_clone_stats_t s;
    return s;
}
#endif

template <typename T>
T* arena_clone(const T* src)
{
    if (src == nullptr) {
        return nullptr;
    }
#ifdef CRANE_ARENA_PROFILE
    arena_clone_stats().calls.fetch_add(1, std::memory_order_relaxed);
#endif
    struct depth_guard {
        depth_guard() { if (++arena_clone_depth() == 1) arena_clone_memo().clear(); }
        ~depth_guard() { --arena_clone_depth(); }
    } guard;

    auto& memo = arena_clone_memo();
    auto  it   = memo.find(static_cast<const void*>(src));
    if (it != memo.end()) {
        return static_cast<T*>(it->second);
    }
#ifdef CRANE_ARENA_PROFILE
    arena_clone_stats().misses.fetch_add(1, std::memory_order_relaxed);
#endif
    // Insert only after the recursive copy fully completes: Coq inductives
    // are well-founded (no cycles), so no nested clone call can re-enter on
    // this same `src` while its own copy is still under construction.
    T* dst = arena_alloc<T>(*src);
    memo.emplace(static_cast<const void*>(src), static_cast<void*>(dst));
    return dst;
}

// -- Shared arena capsules ----------------------------------------------
// Phase 1 (runtime-only, no codegen/Coq surface yet) of the shared-arena-
// capsule design (see ~/crane/docs/shared-arena-capsule-plan.md). A
// `crane::arena` is single-owner: dropping it frees everything in one shot,
// which is exactly wrong for a value that gets stored into a long-lived
// structure (a memo table) and aliased from many places over time — every
// such store would otherwise have to `arena_clone` the whole value into the
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
    arena_scope() : prev_(current_arena_ptr())
    {
        current_arena_ptr() = &a_;
        any_scope_ever_installed().store(true, std::memory_order_relaxed);
    }
    ~arena_scope() { current_arena_ptr() = prev_; }

    arena_scope(const arena_scope&)            = delete;
    arena_scope& operator=(const arena_scope&) = delete;

    arena& get() noexcept { return a_; }

private:
    arena  a_;
    arena* prev_;
};

// RAII: install a *caller-supplied* arena as the current one for the duration
// of this scope (restoring any previous one on exit, so scopes nest).  Unlike
// [arena_scope], this owns nothing: the caller controls the arena's lifetime,
// which lets one arena be reused across several sequential top-level calls
// (amortizing allocation) or be pre-sized/pre-warmed before the calls.
class arena_use_scope {
public:
    explicit arena_use_scope(arena& a) : prev_(current_arena_ptr())
    {
        current_arena_ptr() = &a;
        any_scope_ever_installed().store(true, std::memory_order_relaxed);
    }
    ~arena_use_scope() { current_arena_ptr() = prev_; }

    arena_use_scope(const arena_use_scope&)            = delete;
    arena_use_scope& operator=(const arena_use_scope&) = delete;

private:
    arena* prev_;
};

}  // namespace crane
