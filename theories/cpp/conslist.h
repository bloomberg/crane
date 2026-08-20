// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// conslist.h — crane::list<T>: an immutable, persistent, singly-linked cons list.
//
// This is the natural C++ image of a Coq [list] inductive (and exactly how
// OCaml represents lists): a chain of refcounted cells.  The dominant list
// operation in extracted functional code — [cons] — is O(1), as are
// [head]/[tail]/[drop 1], with full structural sharing (cons never copies the
// tail).  Persistent random-access vectors (immer::flex_vector) instead pay
// O(log n) + allocation on every front-insert, which is catastrophic when cons
// is the hot path.
//
// Trade-off: [app] (++), [length], and nth are O(n) here (vs O(log n) for a
// flex_vector).  Use this when a list is built/consumed head-first (the common
// case for parsers/lexers).
//
// The cell carries its own intrusive (non-atomic) refcount — no separate control
// block and no weak-ref count (Coq lists never take weak references), so a cell
// is just {count, head, next}, the leanest a hand-written cons list would use.
// Single-threaded by design, like the rest of Crane's clone-at-boundary model.
//
// Copies are O(1) (a refcount bump on the head cell).  The destructor and
// assignment operators unlink the spine ITERATIVELY, so destroying a
// million-element list does not recurse a million frames deep and blow the stack.

#pragma once
#include <cstddef>
#include <utility>
#include <iterator>
#include <any>
#include <type_traits>
#include "rc.h"

namespace crane {

// A value-semantic heap box, the cons-list's analogue of immer::box.  Used as
// the [Boxed Element] wrapper for *recursive* element types (e.g. json_value
// inside list<json_value>): it provides the indirection that breaks the type
// cycle, so Crane does not additionally wrap the whole list field in an rc, and
// generated code (and drivers) can treat the element as its bare type via the
// implicit conversions below.  One heap allocation per element, refcount-shared
// on copy — exactly like immer::box.  Non-recursive elements are never boxed.
template <typename T>
class box {
    rc<T> p_;
public:
    using value_type = T;
    box() : p_(make_rc<T>()) {}
    box(const T& v) : p_(make_rc<T>(v)) {}
    box(T&& v) : p_(make_rc<T>(std::move(v))) {}
    const T& get() const noexcept { return *p_; }
    operator const T&() const noexcept { return *p_; }
    const T& operator*() const noexcept { return *p_; }
    const T* operator->() const noexcept { return p_.get(); }
};

template <typename T>
class list {
    struct cell {
        std::size_t rc;   // intrusive non-atomic refcount
        T           head;
        cell*       next; // null == nil
    };
    cell* p_ = nullptr;   // null == nil

    static void incref(cell* c) noexcept { if (c) ++c->rc; }
    // Iteratively release a spine: unlink cells we uniquely own, so a long
    // uniquely-owned list frees in a bounded number of stack frames.
    static void decref(cell* c) noexcept {
        while (c && --c->rc == 0) { cell* n = c->next; delete c; c = n; }
    }

    explicit list(cell* c) noexcept : p_(c) {}  // adopt an existing ref (no bump)

public:
    using value_type = T;

    // -- nil / rule-of-five (all O(1)) ----------------------------------
    list() noexcept = default;                                   // nil
    list(const list& o) noexcept : p_(o.p_) { incref(p_); }
    list(list&& o) noexcept : p_(o.p_) { o.p_ = nullptr; }
    list& operator=(const list& o) noexcept {
        if (p_ != o.p_) { incref(o.p_); decref(p_); p_ = o.p_; }
        return *this;
    }
    list& operator=(list&& o) noexcept {
        if (this != &o) { decref(p_); p_ = o.p_; o.p_ = nullptr; }
        return *this;
    }
    ~list() { decref(p_); }

    // cons: O(1), shares the tail (ownership of t's cell moves into c->next).
    static list cons(T h, list t) {
        cell* c = new cell{1, std::move(h), t.p_};
        t.p_ = nullptr;
        return list(c);
    }

    // Converting constructor from a list<U> (implicit), element-by-element.
    // Reconstructs a concrete list<T> from an element-erased list<std::any>
    // (Crane emits e.g. any_cast<list<any>>(x) where a list<T> is expected in a
    // dependent/SigT context), and generally bridges convertible element types.
    // O(n); only hit at std::any boundaries, never the hot cons path.
    template <typename U,
              typename = std::enable_if_t<!std::is_same_v<U, T>>>
    list(const list<U>& other) {
        std::size_t n = 0;
        for (auto it = other.begin(); it != other.end(); ++it) ++n;
        if (n == 0) return;
        T* tmp = static_cast<T*>(::operator new(n * sizeof(T)));
        std::size_t i = 0;
        for (const U& u : other) { ::new (tmp + i) T(convert_elem(u)); ++i; }
        list r{};
        for (std::size_t k = n; k > 0; --k) r = cons(std::move(tmp[k - 1]), std::move(r));
        for (std::size_t k = 0; k < n; ++k) tmp[k].~T();
        ::operator delete(tmp);
        *this = std::move(r);
    }

    template <typename U>
    static T convert_elem(const U& u) {
        if constexpr (std::is_same_v<U, std::any>) return std::any_cast<T>(u);
        else return static_cast<T>(u);
    }

    // -- observers ------------------------------------------------------
    bool     empty() const noexcept { return !p_; }
    const T& front() const noexcept { return p_->head; }           // head, O(1)
    list     tail()  const noexcept { incref(p_->next); return list(p_->next); } // drop 1, O(1)

    std::size_t size() const noexcept {
        std::size_t n = 0;
        for (cell* c = p_; c; c = c->next) ++n;
        return n;
    }

    // Hand each element of a uniquely-owned spine to [yield] by rvalue, freeing
    // the cell as we go, then drop our reference to whatever shared tail remains.
    // Iterative, so a long list costs a bounded number of stack frames.
    //
    // This is what a generated iterative drain destructor should call for a
    // bare-value container: yielding by rvalue lets the drain MOVE the element
    // into its worklist instead of deep-copying it, and skipping shared cells
    // avoids draining subtrees that are still reachable elsewhere.  The list is
    // left nil, so the subsequent ordinary teardown of the field is a no-op.
    template <typename F>
    void drain_each(F&& yield) {
        cell* c = p_;
        p_ = nullptr;
        while (c && c->rc == 1) {
            cell* n = c->next;
            yield(std::move(c->head));  // head is moved-from; ~cell is now cheap
            delete c;                   // does NOT touch next (raw pointer)
            c = n;
        }
        decref(c);
    }

    // app (++): O(len a).  Rebuilds a's spine on top of b, back-to-front and
    // iteratively (no O(n) recursion).  Shares b unchanged.
    static list app(const list& a, list b) {
        std::size_t n = a.size();
        if (n == 0) return b;
        cell* stackbuf[64];
        cell** arr = (n <= 64) ? stackbuf : new cell*[n];
        std::size_t i = 0;
        for (cell* c = a.p_; c; c = c->next) arr[i++] = c;
        list r = std::move(b);
        while (i) { r = cons(arr[i - 1]->head, std::move(r)); --i; }
        if (arr != stackbuf) delete[] arr;
        return r;
    }

    // push_back (append one at the end): O(n), returns a new list.  Only used by
    // crane_container_cast's non-fast path; never the hot cons path.
    list push_back(T x) const {
        std::size_t n = size();
        cell* stackbuf[64];
        cell** arr = (n <= 64) ? stackbuf : new cell*[n];
        std::size_t i = 0;
        for (cell* c = p_; c; c = c->next) arr[i++] = c;
        list r = cons(std::move(x), list{});
        while (i) { r = cons(arr[i - 1]->head, std::move(r)); --i; }
        if (arr != stackbuf) delete[] arr;
        return r;
    }

    // -- iteration (for Drain, string conversions, driver fingerprints) --
    struct const_iterator {
        cell* c;
        using iterator_category = std::forward_iterator_tag;
        using value_type = T;
        using difference_type = std::ptrdiff_t;
        using pointer = const T*;
        using reference = const T&;
        const T& operator*() const noexcept { return c->head; }
        const T* operator->() const noexcept { return &c->head; }
        const_iterator& operator++() noexcept { c = c->next; return *this; }
        bool operator==(const const_iterator& o) const noexcept { return c == o.c; }
        bool operator!=(const const_iterator& o) const noexcept { return c != o.c; }
    };
    const_iterator begin() const noexcept { return {p_}; }
    const_iterator end()   const noexcept { return {nullptr}; }

    // build from a forward range [first,last) preserving order, O(n), no recursion
    template <typename It>
    static list from_range(It first, It last) {
        std::size_t n = 0;
        for (It it = first; it != last; ++it) ++n;
        if (n == 0) return list{};
        T* tmp = static_cast<T*>(::operator new(n * sizeof(T)));
        std::size_t i = 0;
        for (It it = first; it != last; ++it) { ::new (tmp + i) T(*it); ++i; }
        list r{};
        for (std::size_t k = n; k > 0; --k) r = cons(std::move(tmp[k - 1]), std::move(r));
        for (std::size_t k = 0; k < n; ++k) tmp[k].~T();
        ::operator delete(tmp);
        return r;
    }
};

// Free-function cons whose result element type is DEDUCED FROM THE TAIL, not
// named explicitly.  This mirrors immer's [tail.push_front(head)] and is what
// keeps element typing consistent under Crane's erasure: in a dependent/SigT
// context the tail is a list<std::any>, so this yields a list<std::any> (the
// head is converted to std::any), matching how the surrounding erased code
// extracts it.  Naming the element type explicitly (list<T>::cons) instead would
// force the concrete T and mismatch the erased any_cast<list<std::any>> tail.
template <typename T, typename H>
inline list<T> cons(H&& h, list<T> t) {
    return list<T>::cons(T(std::forward<H>(h)), std::move(t));
}

}  // namespace crane
