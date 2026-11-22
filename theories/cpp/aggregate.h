// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The fields of a plain aggregate -- a generated record, a constructor's
// alternative struct -- seen as a pack, whichever standard the program is
// built as.
//
// C++26 binds them as a pack directly ([auto &[... fs] = x]).  An older
// standard (a BDE build is C++20) counts them -- the most initialisers the
// aggregate takes, each convertible to anything -- and binds that many by
// name, up to [max_fields].
//
// [apply(x, f)] calls [f] with every field of [x] (by reference, const when
// [x] is); [field_count<X>()], [fields_t<X>] (their types, as a tuple),
// [each(x, f)] and [get<K>(x)] are built on it.
#pragma once
#include <cstddef>
#include <tuple>
#include <type_traits>
#include <utility>

namespace crane::aggregate {

#if __cplusplus > 202302L

template <class X, class F> decltype(auto) apply(X &x, F &&f) {
  auto &[... fs] = x;
  return std::forward<F>(f)(fs...);
}

#else

// The most fields an aggregate may have for C++20 to see them.
inline constexpr std::size_t max_fields = 32;

namespace detail {
// An initialiser of any field.  A conversion to the field's own type (not a
// reference) is the one that never competes with a converting constructor
// of the field ([std::optional], [std::function], ...).
struct any_init {
  template <class T> operator T() const noexcept;
};
template <class X, std::size_t... I>
constexpr bool takes(std::index_sequence<I...>) {
  return requires { X{(void(I), any_init{})...}; };
}
template <class X, std::size_t N = 0> constexpr std::size_t count() {
  if constexpr (N > max_fields || !takes<X>(std::make_index_sequence<N + 1>{}))
    return N;
  else
    return count<X, N + 1>();
}
} // namespace detail

template <class X, class F> decltype(auto) apply(X &x, F &&f) {
  constexpr std::size_t N = detail::count<std::remove_cv_t<X>>();
  static_assert(N <= max_fields,
                "crane::aggregate: too many fields to bind under C++20");
  if constexpr (N == 0)
    return std::forward<F>(f)();
  else if constexpr (N == 1) {
    auto &[f0] = x;
    return std::forward<F>(f)(f0);
  } else if constexpr (N == 2) {
    auto &[f0, f1] = x;
    return std::forward<F>(f)(f0, f1);
  } else if constexpr (N == 3) {
    auto &[f0, f1, f2] = x;
    return std::forward<F>(f)(f0, f1, f2);
  } else if constexpr (N == 4) {
    auto &[f0, f1, f2, f3] = x;
    return std::forward<F>(f)(f0, f1, f2, f3);
  } else if constexpr (N == 5) {
    auto &[f0, f1, f2, f3, f4] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4);
  } else if constexpr (N == 6) {
    auto &[f0, f1, f2, f3, f4, f5] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5);
  } else if constexpr (N == 7) {
    auto &[f0, f1, f2, f3, f4, f5, f6] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6);
  } else if constexpr (N == 8) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7);
  } else if constexpr (N == 9) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8);
  } else if constexpr (N == 10) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9);
  } else if constexpr (N == 11) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10);
  } else if constexpr (N == 12) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11);
  } else if constexpr (N == 13) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12);
  } else if constexpr (N == 14) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13);
  } else if constexpr (N == 15) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14);
  } else if constexpr (N == 16) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14,
           f15] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15);
  } else if constexpr (N == 17) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16);
  } else if constexpr (N == 18) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17);
  } else if constexpr (N == 19) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18);
  } else if constexpr (N == 20) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19);
  } else if constexpr (N == 21) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20);
  } else if constexpr (N == 22) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21);
  } else if constexpr (N == 23) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22);
  } else if constexpr (N == 24) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23);
  } else if constexpr (N == 25) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24);
  } else if constexpr (N == 26) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25);
  } else if constexpr (N == 27) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25, f26);
  } else if constexpr (N == 28) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25, f26, f27);
  } else if constexpr (N == 29) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25, f26, f27, f28);
  } else if constexpr (N == 30) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28,
           f29] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25, f26, f27, f28, f29);
  } else if constexpr (N == 31) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29,
           f30] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25, f26, f27, f28, f29, f30);
  } else if constexpr (N == 32) {
    auto &[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
           f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29,
           f30, f31] = x;
    return std::forward<F>(f)(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
                              f12, f13, f14, f15, f16, f17, f18, f19, f20, f21,
                              f22, f23, f24, f25, f26, f27, f28, f29, f30, f31);
  }
}

#endif

// (Named function objects rather than lambdas in an unevaluated operand,
// which clang 22 fails on with a structured binding pack.)
namespace detail {
struct counter {
  template <class... Fs>
  std::integral_constant<std::size_t, sizeof...(Fs)> operator()(Fs &...) const;
};
struct typer {
  template <class... Fs>
  std::type_identity<std::tuple<std::remove_cvref_t<Fs>...>>
  operator()(Fs &...) const;
};
} // namespace detail

template <class X> constexpr std::size_t field_count() {
  return decltype(apply(std::declval<X &>(), detail::counter{}))::value;
}

template <class X>
using fields_t =
    typename decltype(apply(std::declval<X &>(), detail::typer{}))::type;

template <class X, class F> void each(X &x, F &&f) {
  apply(x, [&](auto &...fs) { (f(fs), ...); });
}

template <std::size_t K, class X> auto &get(X &x) {
  return apply(
      x, [](auto &...fs) -> auto & { return std::get<K>(std::tie(fs...)); });
}

} // namespace crane::aggregate
