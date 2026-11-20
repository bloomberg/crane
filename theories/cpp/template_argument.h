// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::template_argument_t<T, I>: the I-th type argument of the class
// template specialisation T names, references and cv-qualifiers removed.  A
// typed mapping's view conversion names a component's C++ type
// (%stored(c)); where Crane does not know the type a value was declared at
// (a structured binding), it reads the component back from the value's
// canonical type with this.

#pragma once

#include <cstddef>
#include <tuple>
#include <type_traits>

namespace crane {

template <class T, std::size_t I> struct template_argument;

template <template <class...> class C, class... Ts, std::size_t I>
struct template_argument<C<Ts...>, I> {
  using type = std::tuple_element_t<I, std::tuple<Ts...>>;
};

template <class T, std::size_t I>
using template_argument_t =
    typename template_argument<std::remove_cvref_t<T>, I>::type;

} // namespace crane
