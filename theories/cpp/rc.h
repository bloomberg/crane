// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// rc.h — single-allocation, Rust-like rc<T>/weak<T> for C++ (single-threaded)
// GENERATED USING GPT-5
// - **Single allocation**: control block and T live in one heap block
// - Non-atomic counts (like Rust's rc). Not thread-safe.
// - weak<T> supported to break cycles. No enable_shared_from_this, by design.
// - Intentionally minimal; extend with custom allocators/deleters as needed.

#pragma once
#include <cstddef>
#include <utility>
#include <type_traits>
#include <new>
#include <cassert>
#include <memory>
// The non-atomic [crane::rc] participates in the runtime scoped-arena feature
// (arena.h) only when the [Set Crane Arena] master switch is on, in which case
// the generated header defines CRANE_ARENA before including this file.  Under
// that switch [rc<T>::make] bump-allocates from the current arena when a scope
// is open, keeping the region alive through a keeper stored in the control
// block.  arena.h has no dependency on rc.h, so this include is one-directional.
// When the switch is off, rc.h carries no arena machinery at all.
#ifdef CRANE_ARENA
#include "arena.h"
#endif

namespace crane {

// Forward declarations
template <typename T> class rc;
template <typename T> class weak;
template <typename T> class enable_rc_from_this;

template <typename T>
struct ControlBlock {
    std::size_t strong{1}; // number of owning rc
    std::size_t weak{0};   // number of weak

    // Raw storage for T. We construct/destroy T manually via placement new.
    // Kept as the first-after-counts member so [offsetof(ControlBlock<T>,
    // storage)] (used by enable_rc_from_this) is unaffected by the arena fields
    // appended below.
    alignas(T) unsigned char storage[sizeof(T)];

#ifdef CRANE_ARENA
    // Runtime scoped-arena backing (see arena.h), compiled in only under the
    // [Set Crane Arena] master switch.  When [arena_backed] is true this control
    // block's memory is owned by an arena (bump-allocated by [rc<T>::make], never
    // [new]/[delete]d), and [arena_keeper] keeps that arena alive as long as this
    // block is strongly referenced.  For ordinary heap blocks (make_rc) these
    // stay default (false / null) and cost only their storage.  When the switch
    // is off these fields are absent entirely, so ControlBlock<T> is exactly the
    // two counts plus storage.
    std::shared_ptr<arena> arena_keeper{};
    bool                   arena_backed{false};
#endif

    T*       ptr()       noexcept { return reinterpret_cast<T*>(&storage[0]); }
    const T* ptr() const noexcept { return reinterpret_cast<const T*>(&storage[0]); }
};

// Factory

template <typename T, typename... Args>
rc<T> make_rc(Args&&... args);

// rc<T> — owning reference-counted pointer (like Rust Rc<T>)

template <typename T>
class rc {
public:
    using element_type = T;

    rc() noexcept = default; // null rc

    // Null rc from [nullptr] (non-explicit), so generated code like
    // [cond ? make_rc<T>(...) : nullptr] type-checks, matching std::shared_ptr.
    rc(std::nullptr_t) noexcept {}

    rc(const rc& other) noexcept : ctrl_(other.ctrl_) { inc_strong(); }
    rc(rc&& other) noexcept : ctrl_(other.ctrl_) { other.ctrl_ = nullptr; }

    // Construct from weak if still alive
    explicit rc(const weak<T>& weak) noexcept : ctrl_(weak.ctrl_) {
        if (!ctrl_ || ctrl_->strong == 0) { ctrl_ = nullptr; return; }
        inc_strong();
    }

    rc& operator=(const rc& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; inc_strong(); }
        return *this;
    }

    rc& operator=(rc&& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; other.ctrl_ = nullptr; }
        return *this;
    }

    ~rc() { release(); }

    T* get() const noexcept { return ctrl_ ? ctrl_->ptr() : nullptr; }
    T& operator*() const noexcept { assert(get()); return *get(); }
    T* operator->() const noexcept { return get(); }
    explicit operator bool() const noexcept { return get() != nullptr; }

    std::size_t use_count() const noexcept { return ctrl_ ? ctrl_->strong : 0; }

    void reset() noexcept { release(); }

    void swap(rc& other) noexcept { std::swap(ctrl_, other.ctrl_); }

    weak<T> downgrade() const noexcept; // like Rc::downgrade() in Rust

    // Arena-aware factory (runtime scoped-arena feature, arena.h).  When a
    // [crane::arena_scope] / [crane::arena_use_scope] is open on this thread the
    // control block (and T inside it) is bump-allocated from the current arena
    // and, for an owning scope, keeps that region alive via a keeper stored in
    // the block; otherwise this is exactly [crane::make_rc<T>].  Copying the
    // resulting rc is an O(1) refcount bump in both cases, so no deep clone is
    // ever needed.
    template <typename... Args>
    static rc<T> make(Args&&... args);

private:
    template <typename U, typename... Args>
    friend rc<U> make_rc(Args&&... args);
    template <typename U, typename... Args>
    friend rc<U> make_rc_reusing(rc<U> token, Args&&... args);
    friend class weak<T>;
    template <typename U> friend class enable_rc_from_this;

    explicit rc(ControlBlock<T>* ctrl) noexcept : ctrl_(ctrl) {}

    void inc_strong() noexcept { if (ctrl_) { ++ctrl_->strong; } }

    void release() noexcept {
        if (!ctrl_) return;
        assert(ctrl_->strong > 0);
        if (--ctrl_->strong == 0) {
#ifdef CRANE_ARENA
            if (ctrl_->arena_backed) {
                // Region-owned block: never [delete] it.  Move the keeper out
                // *before* running ~T and dropping it, so that if dropping the
                // last keeper frees the arena (and with it this very control
                // block), no freed memory is touched afterward.  ~T runs while
                // [keeper] still holds the region alive, so T's own fields
                // (child rc's into the same region) are released safely.
                std::shared_ptr<arena> keeper = std::move(ctrl_->arena_keeper);
                ctrl_->ptr()->~T();
                ctrl_ = nullptr;
                return; // [keeper] drops here, possibly freeing the region.
            }
#endif
            // Destroy T in-place
            ctrl_->ptr()->~T();
            if (ctrl_->weak == 0) {
                delete ctrl_;
                ctrl_ = nullptr;
                return;
            }
        }
        ctrl_ = nullptr;
    }

    ControlBlock<T>* ctrl_{nullptr};
};

// weak<T> — non-owning observer

template <typename T>
class weak {
public:
    weak() noexcept = default;
    weak(const weak& other) noexcept : ctrl_(other.ctrl_) { inc_weak(); }
    weak(weak&& other) noexcept : ctrl_(other.ctrl_) { other.ctrl_ = nullptr; }

    weak& operator=(const weak& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; inc_weak(); }
        return *this;
    }

    weak& operator=(weak&& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; other.ctrl_ = nullptr; }
        return *this;
    }

    ~weak() { release(); }

    bool expired() const noexcept { return !ctrl_ || ctrl_->strong == 0; }
    rc<T> lock() const noexcept { return rc<T>(*this); }
    void reset() noexcept { release(); }

private:
    friend class rc<T>;

    explicit weak(ControlBlock<T>* ctrl) noexcept : ctrl_(ctrl) { inc_weak(); }

    void inc_weak() noexcept { if (ctrl_) { ++ctrl_->weak; } }

    void release() noexcept {
        if (!ctrl_) return;
        assert(ctrl_->weak > 0);
        // Never [delete] an arena-backed block: the region owns its memory.
        // (Arena-backed values are acyclic Coq inductives that do not use weak
        // refs; a weak ref into a region that has already been freed is out of
        // scope for this feature, same as the pre-redesign arena representation.)
        if (--ctrl_->weak == 0 && ctrl_->strong == 0
#ifdef CRANE_ARENA
            && !ctrl_->arena_backed
#endif
           ) {
            delete ctrl_;
            ctrl_ = nullptr;
            return;
        }
        ctrl_ = nullptr;
    }

    ControlBlock<T>* ctrl_{nullptr};
};

// rc::downgrade implementation

template <typename T>
weak<T> rc<T>::downgrade() const noexcept { return weak<T>(ctrl_); }

// enable_rc_from_this<T> — analogue of std::enable_shared_from_this for rc<T>.
// A type T that derives from enable_rc_from_this<T> gains rc_from_this(), which
// returns an owning rc<T> to itself. Instead of storing a self-weak (which would
// be destroyed *during* ~T and, with this single-block scheme, free the control
// block mid-destruction), it recovers the control block from the object's own
// address. Valid only for objects created via make_rc<T> — which is exactly how
// Crane-extracted recursive values are always allocated.
template <typename T>
class enable_rc_from_this {
protected:
    enable_rc_from_this() noexcept                                  = default;
    enable_rc_from_this(const enable_rc_from_this&) noexcept        = default;
    enable_rc_from_this& operator=(const enable_rc_from_this&) noexcept = default;
    ~enable_rc_from_this()                                          = default;

public:
    rc<T> rc_from_this() const noexcept {
        T* self = const_cast<T*>(static_cast<const T*>(this));
        auto* ctrl = reinterpret_cast<ControlBlock<T>*>(
            reinterpret_cast<unsigned char*>(self)
            - offsetof(ControlBlock<T>, storage));
        ++ctrl->strong;
        return rc<T>(ctrl);
    }
};

// make_rc implementation (single allocation: one new for control + T)

template <typename T, typename... Args>
rc<T> make_rc(Args&&... args) {
    static_assert(!std::is_array<T>::value, "rc<T> does not support arrays");
    auto* ctrl = new ControlBlock<T>();
    try {
        ::new (static_cast<void*>(ctrl->ptr())) T(std::forward<Args>(args)...);
    } catch (...) {
        delete ctrl;
        throw;
    }
    return rc<T>(ctrl);
}

// Perceus-style drop-guided reuse.  If [token] is the sole owner of its cell
// (strong==1, weak==0, not arena-backed), recycle that cell for a fresh T:
// destroy the old T and placement-construct the new one in place — no
// allocation, no free.  Otherwise fall back to make_rc and let [token] drop
// normally.  The construction args are fully evaluated before the old T is
// destroyed (the caller passes already-computed values, e.g. the recursion
// result), so no aliasing hazard.  Emitted by the codegen for a matched,
// uniquely-owned recursive child threaded as a reuse token to a same-type
// constructor's recursive field.
template <typename T, typename... Args>
rc<T> make_rc_reusing(rc<T> token, Args&&... args) {
    static_assert(!std::is_array<T>::value, "rc<T> does not support arrays");
    ControlBlock<T>* c = token.ctrl_;
    if (c && c->strong == 1 && c->weak == 0
#ifdef CRANE_ARENA
        && !c->arena_backed
#endif
    ) {
        token.ctrl_ = nullptr;         // adopt the block; suppress token's dtor
        c->ptr()->~T();                // destroy the old payload in place
        try {
            ::new (static_cast<void*>(c->ptr())) T(std::forward<Args>(args)...);
        } catch (...) {
            delete c;
            throw;
        }
        return rc<T>(c);               // strong stays 1 — reused in place
    }
    return make_rc<T>(std::forward<Args>(args)...);  // token drops at return
}

// rc<T>::make — arena-aware factory (see the in-class declaration).
template <typename T>
template <typename... Args>
rc<T> rc<T>::make(Args&&... args) {
    static_assert(!std::is_array<T>::value, "rc<T> does not support arrays");
#ifdef CRANE_ARENA
    arena* ap = current_arena_ptr();
    if (ap == nullptr) {
        // No scope open: ordinary single-allocation heap rc.
        return make_rc<T>(std::forward<Args>(args)...);
    }
    // A scope is open: bump-allocate the control block (and T inside it) from
    // the region.  Grab the keeper first (null under a caller-owned scope).
    std::shared_ptr<arena> keeper = acquire_arena_keeper();
    void* mem = ap->resource()->allocate(sizeof(ControlBlock<T>),
                                         alignof(ControlBlock<T>));
    auto* ctrl = ::new (mem) ControlBlock<T>();
    ctrl->arena_backed = true;
    ctrl->arena_keeper = std::move(keeper);
    ::new (static_cast<void*>(ctrl->ptr())) T(std::forward<Args>(args)...);
    ++arena_bump_count();
    return rc<T>(ctrl);
#else
    // Arena machinery not compiled in ([Set Crane Arena] off): make() is just
    // the ordinary heap factory.  (Generated code only ever calls make() when
    // the switch is on, but keep a correct definition so rc.h is self-contained.)
    return make_rc<T>(std::forward<Args>(args)...);
#endif
}

} // namespace crane

// Overload of [crane_raw] (declared in crane_fn.h for std::shared_ptr<T> / T*)
// for the non-atomic [crane::rc<T>]: extract the raw pointer. Kept here so it is
// available whenever rc<T> is in use (with or without crane_fn.h included), so
// loopify's raw-pointer extraction works uniformly across pointer flavors.
template <typename T> T *crane_raw(const crane::rc<T> &p) noexcept {
  return p.get();
}

/*
Usage example:

#include "rc.h"
#include <iostream>
using namespace crane;

struct Node {
    int value;
    weak<Node> parent;         // break cycles
    rc<Node> left, right;      // children own their subtrees
    explicit Node(int v): value(v) {}
    ~Node(){ std::cout << "drop Node(" << value << ")
"; }
};

int main(){
    auto root = make_rc<Node>(1);
    root->left = make_rc<Node>(2);
    root->left->parent = root.downgrade();

    std::cout << root.use_count() << "
"; // 1
}
*/
