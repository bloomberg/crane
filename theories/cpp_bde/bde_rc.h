// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// bde_rc.h — single-allocation, Rust-like rc<T>/weak<T> implemented with BDE
// - Uses BDE allocators (bslma::Allocator / bslma::Default)
// - Single allocation: control block + T are in one block
// - Non-atomic (single-threaded) ref counts like Rust's Rc
// - weak<T> to break cycles
// - Minimal, header-only example — tailor to your codebase conventions

#pragma once

#include <bsl_cstddef.h>          // bsl::size_t
#include <bsl_utility.h>          // bsl::forward, bsl::move
#include <bsl_algorithm.h>        // bsl::swap
#include <bslmf_isarray.h>        // bsl::is_array

#include <bslma_allocator.h>
#include <bslma_default.h>

#include <bsls_assert.h>
#include <bsls_objectbuffer.h>    // bsls::ObjectBuffer<T>

using namespace BloombergLP;

namespace crane {

// Forward decls
template <class T> class rc;
template <class T> class weak;

template <class T>
struct ControlBlock {
    bsl::size_t       d_strong;     // number of owning rc
    bsl::size_t       d_weak;       // number of weak
    bslma::Allocator* d_allocator;  // allocator used for this block
    bsls::ObjectBuffer<T> d_storage; // raw storage for T

    ControlBlock(bslma::Allocator* allocator)
    : d_strong(1)
    , d_weak(0)
    , d_allocator(allocator)
    {}

    T*       ptr()       { return d_storage.address(); }
    const T* ptr() const { return d_storage.address(); }
};

// Factory — allocator-aware (defaults to bslma::Default::allocator())
// Overloads:
//  1) make_rc(args...)                       -> uses default allocator
//  2) make_rc(Allocator* alloc, args...)     -> uses provided allocator (overload)
// NOTE: If T's *first* constructor parameter is also 'bslma::Allocator*', this
//       overload can be selected unintentionally. If that’s a concern, use the
//       tag-dispatched form below instead.

struct WithAllocTag { };
static const WithAllocTag withAlloc = WithAllocTag();

// Tag-dispatched form (always unambiguous):
//   make_rc(withAlloc, alloc, args...)

template <class T, class... Args>
rc<T> make_rc(Args&&... args);

template <class T, class... Args>
rc<T> make_rc(bslma::Allocator* allocator, Args&&... args);

template <class T, class... Args>
rc<T> make_rc(WithAllocTag, bslma::Allocator* allocator, Args&&... args);

// rc<T>

template <class T>
class rc {
  public:
    // TYPES
    typedef T element_type;

    // CREATORS
    rc() BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(0) {}

    rc(const rc& other) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(other.d_ctrl_p) {
        incStrong();
    }

    rc(rc&& other) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(other.d_ctrl_p) {
        other.d_ctrl_p = 0;
    }

    explicit rc(const weak<T>& weak) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(weak.d_ctrl_p) {
        if (!d_ctrl_p || d_ctrl_p->d_strong == 0) { d_ctrl_p = 0; return; }
        incStrong();
    }

    ~rc() { release(); }

    // MANIPULATORS
    rc& operator=(const rc& rhs) BSLS_KEYWORD_NOEXCEPT {
        if (this != &rhs) {
            release();
            d_ctrl_p = rhs.d_ctrl_p;
            incStrong();
        }
        return *this;
    }

    rc& operator=(rc&& rhs) BSLS_KEYWORD_NOEXCEPT {
        if (this != &rhs) {
            release();
            d_ctrl_p = rhs.d_ctrl_p;
            rhs.d_ctrl_p = 0;
        }
        return *this;
    }

    void reset() BSLS_KEYWORD_NOEXCEPT { release(); }

    void swap(rc& other) BSLS_KEYWORD_NOEXCEPT { bsl::swap(d_ctrl_p, other.d_ctrl_p); }

    weak<T> downgrade() const BSLS_KEYWORD_NOEXCEPT; // non-owning view

    // ACCESSORS
    T* get() const BSLS_KEYWORD_NOEXCEPT { return d_ctrl_p ? d_ctrl_p->ptr() : 0; }
    T& operator*()  const BSLS_KEYWORD_NOEXCEPT { BSLS_ASSERT(get()); return *get(); }
    T* operator->() const BSLS_KEYWORD_NOEXCEPT { return get(); }

    explicit operator bool() const BSLS_KEYWORD_NOEXCEPT { return get() != 0; }

    bsl::size_t useCount() const BSLS_KEYWORD_NOEXCEPT { return d_ctrl_p ? d_ctrl_p->d_strong : 0; }

  private:
    // FRIENDS
    template <class U, class... Args>
    friend rc<U> make_rc(Args&&...);

    template <class U, class... Args>
    friend rc<U> make_rc(bslma::Allocator*, Args&&...);

    template <class U, class... Args>
    friend rc<U> make_rc(WithAllocTag, bslma::Allocator*, Args&&...);

    friend class weak<T>;

    // CREATORS (private)
    explicit rc(ControlBlock<T>* ctrl) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(ctrl) {}

    // HELPER
    void incStrong() BSLS_KEYWORD_NOEXCEPT { if (d_ctrl_p) { ++d_ctrl_p->d_strong; } }

    void release() BSLS_KEYWORD_NOEXCEPT {
        if (!d_ctrl_p) return;
        BSLS_ASSERT(d_ctrl_p->d_strong > 0);
        if (--d_ctrl_p->d_strong == 0) {
            // destroy T in-place
            d_ctrl_p->ptr()->~T();
            if (d_ctrl_p->d_weak == 0) {
                // destroy control block and free memory
                bslma::Allocator* alloc = d_ctrl_p->d_allocator;
                d_ctrl_p->~ControlBlock<T>();
                alloc->deallocate(d_ctrl_p);
                d_ctrl_p = 0;
                return;
            }
        }
        d_ctrl_p = 0;
    }

  private:
    ControlBlock<T>* d_ctrl_p; // not owning when counts go to zero
};

// weak<T>

template <class T>
class weak {
  public:
    weak() BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(0) {}

    weak(const weak& other) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(other.d_ctrl_p) { incweak(); }

    weak(weak&& other) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(other.d_ctrl_p) { other.d_ctrl_p = 0; }

    ~weak() { release(); }

    weak& operator=(const weak& rhs) BSLS_KEYWORD_NOEXCEPT {
        if (this != &rhs) {
            release();
            d_ctrl_p = rhs.d_ctrl_p;
            incweak();
        }
        return *this;
    }

    weak& operator=(weak&& rhs) BSLS_KEYWORD_NOEXCEPT {
        if (this != &rhs) {
            release();
            d_ctrl_p = rhs.d_ctrl_p;
            rhs.d_ctrl_p = 0;
        }
        return *this;
    }

    bool expired() const BSLS_KEYWORD_NOEXCEPT { return !d_ctrl_p || d_ctrl_p->d_strong == 0; }

    rc<T> lock() const BSLS_KEYWORD_NOEXCEPT { return rc<T>(*this); }

    void reset() BSLS_KEYWORD_NOEXCEPT { release(); }

  private:
    friend class rc<T>;

    explicit weak(ControlBlock<T>* ctrl) BSLS_KEYWORD_NOEXCEPT : d_ctrl_p(ctrl) { incweak(); }

    void incweak() BSLS_KEYWORD_NOEXCEPT { if (d_ctrl_p) { ++d_ctrl_p->d_weak; } }

    void release() BSLS_KEYWORD_NOEXCEPT {
        if (!d_ctrl_p) return;
        BSLS_ASSERT(d_ctrl_p->d_weak > 0);
        if (--d_ctrl_p->d_weak == 0 && d_ctrl_p->d_strong == 0) {
            bslma::Allocator* alloc = d_ctrl_p->d_allocator;
            d_ctrl_p->~ControlBlock<T>();
            alloc->deallocate(d_ctrl_p);
            d_ctrl_p = 0;
            return;
        }
        d_ctrl_p = 0;
    }

  private:
    ControlBlock<T>* d_ctrl_p; // non-owning handle
};

// rc::downgrade

template <class T>
weak<T> rc<T>::downgrade() const BSLS_KEYWORD_NOEXCEPT { return weak<T>(d_ctrl_p); }

// Factories

template <class T, class... Args>
rc<T> make_rc(Args&&... args) {
    return make_rc<T>(bslma::Default::allocator(0), bsl::forward<Args>(args)...);
}

template <class T, class... Args>
rc<T> make_rc(bslma::Allocator* allocator, Args&&... args) {
    return make_rc<T>(withAlloc, allocator, bsl::forward<Args>(args)...);
}

template <class T, class... Args>
rc<T> make_rc(WithAllocTag, bslma::Allocator* allocator, Args&&... args) {
    BSLS_ASSERT_SAFE(allocator);
    static_assert(!bsl::is_array<T>::value, "rc<T> does not support arrays");

    // allocate raw memory for control block
    void* mem = allocator->allocate(sizeof(ControlBlock<T>));

    ControlBlock<T>* ctrl = 0;

    // construct control block
    ctrl = new (mem) ControlBlock<T>(allocator);

    // now construct T in-place; if this throws, clean up control block
    try {
        ::new (ctrl->ptr()) T(bsl::forward<Args>(args)...);
    } catch (...) {
        ctrl->~ControlBlock<T>();
        allocator->deallocate(mem);
        throw;
    }

    return rc<T>(ctrl);
}

} // namespace crane

/*
USAGE EXAMPLE

#include "bde_rc.h"
#include <bsl_iostream.h>

using namespace crane;

struct Node {
    int value;
    weak<Node> parent;         // break cycles
    rc<Node> left, right;      // children own their subtrees

    explicit Node(int v): value(v) {}
    ~Node(){ bsl::cout << "drop Node(" << value << ")\n"; }
};

int main(){
    bslma::Allocator* alloc = bslma::Default::allocator(0);

    rc<Node> root = make_rcA<Node>(alloc, 1);
    root->left = make_rcA<Node>(alloc, 2);
    root->left->parent = root.downgrade();

    bsl::cout << root.useCount() << "\n"; // 1
}
*/
