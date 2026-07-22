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

// Runtime helper for calling a genuinely-concrete callable [f] with
// arguments that may be boxed as [std::any] even though [f] does not accept
// [std::any] directly.
//
// This arises when a value-dependent parameter (e.g. a functor's abstract
// [S.sem a]) is destructured from a type-erased carrier (a [std::pair<any,
// any>] built for a generic domain), so the resulting value is statically
// [std::any] at the call site.  The callee [f], however, is only concrete at
// C++ template instantiation time (e.g. a functor parameter deduced from a
// caller-supplied lambda with a concrete signature like
// [bool(std::string, std::string)]).  Crane cannot know at OCaml translation
// time whether [f] will end up generic (accepts [std::any] as-is) or
// concrete (needs each boxed argument unwrapped with
// [std::any_cast<ParamType>]), so the decision is deferred to C++ via
// [std::function] CTAD, same trick as [crane_erase_fn].
template <class Sig, std::size_t I> struct crane_fn_param;
template <class R, class... P, std::size_t I>
struct crane_fn_param<std::function<R(P...)>, I> {
  using type = std::tuple_element_t<I, std::tuple<P...>>;
};

template <class Sig, std::size_t I, class A>
decltype(auto) crane_call_erased_unbox(A &&a) {
  using T = typename crane_fn_param<Sig, I>::type;
  if constexpr (std::is_same_v<std::decay_t<A>, std::any> &&
                !std::is_same_v<std::decay_t<T>, std::any>) {
    return std::any_cast<T>(std::forward<A>(a));
  } else {
    return std::forward<A>(a);
  }
}

template <class F, class... Args, std::size_t... I>
decltype(auto) crane_call_erased_dispatch(std::index_sequence<I...>, F &&f,
                                           Args &&...args) {
  using Sig = decltype(std::function{f});
  return f(crane_call_erased_unbox<Sig, I>(std::forward<Args>(args))...);
}

template <class F, class... Args>
decltype(auto) crane_call_erased(F &&f, Args &&...args) {
  if constexpr (requires { std::function{f}; }) {
    return crane_call_erased_dispatch(std::index_sequence_for<Args...>{},
                                       std::forward<F>(f),
                                       std::forward<Args>(args)...);
  } else {
    return f(std::forward<Args>(args)...);
  }
}
