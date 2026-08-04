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
    // actually reached, so an embedding that forgot to install an [arena_scope]
    // (and would therefore grow this never-resetting region unboundedly) at
    // least gets a signal in development.  Release builds compile this away
    // entirely, so the fallback stays zero-overhead there.
    static thread_local bool warned = false;
    if (!warned) {
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

// RAII: install a fresh arena as the current one for the duration of this scope
// (restoring any previous one on exit, so scopes nest).
class arena_scope {
public:
    arena_scope() : prev_(current_arena_ptr()) { current_arena_ptr() = &a_; }
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
    }
    ~arena_use_scope() { current_arena_ptr() = prev_; }

    arena_use_scope(const arena_use_scope&)            = delete;
    arena_use_scope& operator=(const arena_use_scope&) = delete;

private:
    arena* prev_;
};

}  // namespace crane
