// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Runtime helper for storing a concrete callable into a type-erased
// [std::any] field.
//
// When a value-dependent function type is erased to [std::any], the
// application site reads the callable back with
// [std::any_cast<std::function<std::any(std::any...)>>], so the construction
// site must store that same canonical representation rather than the raw
// closure (otherwise [any_cast] throws [std::bad_any_cast]).
//
// [crane_erase_fn] adapts an arbitrary callable to
// [std::function<std::any(std::any...)>] and boxes the result into [std::any].
// Two cases:
//
//   * Concrete-signature callables (a named function, a monomorphic lambda,
//     etc.): [std::function] CTAD deduces the signature [R(A...)], and the
//     adapter unboxes each argument with [std::any_cast<A>].
//
//   * Generic lambdas (e.g. [ [](const auto&){...} ], produced when a function's
//     domain is a value-dependent/abstract type erased to [std::any]): CTAD
//     cannot deduce a signature, so the callable is wrapped as a unary
//     [any -> any] adapter that forwards the boxed argument directly (a generic
//     lambda accepts the [std::any] as its [const auto&] parameter).
//
// Emitted as a global (like [ITree] in crane_itree.h) rather than in
// [namespace crane] so the extractor can reference it with a plain identifier.
#pragma once
#include <any>
#include <functional>
#include <type_traits>
#include <utility>

template <class R, class... A>
std::function<std::any(std::conditional_t<true, std::any, A>...)>
crane_erase_fn_impl(std::function<R(A...)> f) {
  return [f = std::move(f)](
             std::conditional_t<true, std::any, A>... as) mutable -> std::any {
    if constexpr (std::is_void_v<R>) {
      f(std::any_cast<A>(as)...);
      return std::any{};
    } else {
      return std::any(f(std::any_cast<A>(as)...));
    }
  };
}

template <class F> auto crane_erase_fn(F &&f) {
  if constexpr (requires { std::function{std::forward<F>(f)}; }) {
    return crane_erase_fn_impl(std::function{std::forward<F>(f)});
  } else {
    return std::function<std::any(std::any)>(
        [f = std::forward<F>(f)](std::any a) mutable -> std::any {
          if constexpr (std::is_void_v<decltype(f(a))>) {
            f(a);
            return std::any{};
          } else {
            return std::any(f(a));
          }
        });
  }
}
