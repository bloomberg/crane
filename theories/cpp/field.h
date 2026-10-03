// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::field<T>: how `Set Crane BoxedFields` stores a constructor field
// whose type is one of the inductive's type parameters.
//
// Where the field is declared its type is a parameter, so whether boxing it
// pays is a question about each instantiation, answered here: a T whose copy
// is as cheap as a pointer's (a scalar, a smart pointer, a lazy cell, an
// erased crane::obj) is stored as it is, and anything else -- an inductive
// value, a std::pair of them, a string -- behind one shared, immutable heap
// cell, so copying, moving or destroying the value that holds the field
// stops at the cell.  That is OCaml's representation for such a field.
//
// crane::unbox reads either the same way, as a const T&.

#ifndef INCLUDED_CRANE_FIELD
#define INCLUDED_CRANE_FIELD

#include <cstddef>
#include <memory>
#include <type_traits>
#include <utility>

#include "shared_block.h"

namespace crane {

// Whether copying a T costs no more than copying a pointer.  A type says so
// of itself by declaring [crane_cheap_copy] (Crane's handles do, and so does
// every generated coinductive type, a lazy cell).
template <class T, class = void>
struct copy_is_cheap
    : std::bool_constant<std::is_trivially_copyable_v<T> &&
                         sizeof(T) <= 2 * sizeof(void *)> {};
template <class T>
struct copy_is_cheap<T, std::void_t<typename T::crane_cheap_copy>> : std::true_type {};
template <class T> struct copy_is_cheap<std::shared_ptr<T>> : std::true_type {};

CRANE_RC_POLICY_BEGIN

// One shared, immutable cell holding a T.
template <class T> class field_box {
  struct cell : shared_block {
    T value;
    template <class... A>
    explicit cell(A &&...a) : shared_block{{}, &drop}, value(std::forward<A>(a)...) {}
    static void drop(const void *b) noexcept {
      delete static_cast<const cell *>(static_cast<const shared_block *>(b));
    }
  };
  const cell *p_;

public:
  using crane_cheap_copy = void;

  field_box() : p_(new cell()) {}
  field_box(const T &v) : p_(new cell(v)) {}
  field_box(T &&v) : p_(new cell(std::move(v))) {}

  field_box(const field_box &o) noexcept : p_(o.p_) { p_->retain(); }
  field_box(field_box &&o) noexcept : p_(std::exchange(o.p_, nullptr)) {}
  field_box &operator=(const field_box &o) noexcept {
    field_box copy(o);
    std::swap(p_, copy.p_);
    return *this;
  }
  field_box &operator=(field_box &&o) noexcept {
    field_box taken(std::move(o));
    std::swap(p_, taken.p_);
    return *this;
  }
  ~field_box() {
    if (p_)
      p_->release();
  }

  const T &operator*() const noexcept { return p_->value; }
  const T *operator->() const noexcept { return &p_->value; }
  operator const T &() const noexcept { return p_->value; }
};

CRANE_RC_POLICY_END

template <class T>
using field = std::conditional_t<copy_is_cheap<T>::value, T, field_box<T>>;

template <class T> const T &unbox(const T &v) noexcept { return v; }
template <class T> const T &unbox(const field_box<T> &b) noexcept { return *b; }

} // namespace crane

#endif // INCLUDED_CRANE_FIELD
