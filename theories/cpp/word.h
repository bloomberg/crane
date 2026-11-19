// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Which types are a word that names its own block.
//
// A shared variant's value (shared_variant.h) is one word: 0, an odd tag, or
// the address of a counted block whose [destroy] says which alternative it
// holds.  So, given such a word, the type can tell whether a block is one of
// its own.  A generated inductive holding nothing but a shared variant is the
// same word, and so is an aggregate whose one field is such a word -- a
// coinductive's constructor around its interaction-tree layer.  These are
// the *word owners*: [crane::lazy] holds a value of one in its own word,
// rather than in a node of its own, since it can tell that value apart from
// the address of a node (lazy.h).
//
// A word owner [U] answers [crane_owns_destroy(d)]: whether [d] is the
// [destroy] of one of its blocks.
#pragma once
#include <cstddef>
#include <type_traits>
#include <utility>

namespace crane::word_detail {

// The fields of an aggregate, as a type list: its count and first type.
// (Named functions rather than lambdas in an unevaluated operand, which
// clang 22 fails on with a structured binding pack.)
template <class... F> struct fields {
  static constexpr std::size_t count = sizeof...(F);
};
template <class X> auto fields_of(X &x) {
  auto &[... fs] = x;
  return fields<std::remove_cvref_t<decltype(fs)>...>{};
}
template <class X> using fields_t = decltype(fields_of(std::declval<X &>()));
template <class X> constexpr std::size_t field_count() { return fields_t<X>::count; }
template <class L> struct first;
template <class F0, class... F> struct first<fields<F0, F...>> {
  using type = F0;
};
template <class X> using first_field_t = typename first<fields_t<X>>::type;

template <class U> constexpr bool is_word_owner();

// An aggregate of one word whose one field is a word owner.
template <class X> constexpr bool is_owner_aggregate() {
  if constexpr (sizeof(X) != sizeof(void *) || !std::is_aggregate_v<X> || std::is_array_v<X>)
    return false;
  else if constexpr (field_count<X>() != 1)
    return false;
  else
    return is_word_owner<first_field_t<X>>();
}

template <class U> constexpr bool is_word_owner() {
  if constexpr (!std::is_class_v<U> || sizeof(U) != sizeof(void *))
    return false;
  else if constexpr (requires { typename U::crane_word_owner; })
    return true;
  else if constexpr (requires { typename U::variant_t::crane_word_owner; })
    return true;
  else
    return is_owner_aggregate<U>();
}

// Whether [d] destroys a block of the word owner [U].
template <class U, class D> bool owns_destroy(D d) noexcept {
  if constexpr (requires { typename U::crane_word_owner; })
    return U::crane_owns_destroy(d);
  else if constexpr (requires { typename U::variant_t::crane_word_owner; })
    return U::variant_t::crane_owns_destroy(d);
  else
    return owns_destroy<first_field_t<U>>(d);
}

} // namespace crane::word_detail
