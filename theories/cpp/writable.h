// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::writable(v).ref(): a mutable lvalue holding v, for an argument a
// callee writes or replaces in place (a typed mapping's Replace, or a write
// of a mutable value, taken as T&) when the caller's argument is not a
// variable it may write -- a call's result, or a value it only borrows.
//
// The slot is a temporary, so it lives to the end of the full expression
// holding the call, and whatever the callee writes there is dropped with it:
// the caller's own value is never written through a copy.

#pragma once

#include <type_traits>
#include <utility>

namespace crane {

template <class T> struct writable_slot {
  T value;
  T &ref() noexcept { return value; }
};

template <class V> writable_slot<std::remove_cvref_t<V>> writable(V &&v) {
  return {std::forward<V>(v)};
}

} // namespace crane
