// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Runtime helper for storing a concrete callable into a type-erased
// [std::any] field.
#pragma once
#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <vector>
//
// When a value-dependent function type is erased to [std::any], the
// application site reads the callable back with
// [std::any_cast<std::function<std::any(std::any...)>>], so the construction
// site must store that same canonical representation rather than the raw
// closure (otherwise [any_cast] throws [std::bad_any_cast]).
//
// [crane_raw] extracts a raw pointer from either a std::shared_ptr<T> (via
// .get()) or an already-raw T* (identity), chosen by overload resolution.
// Loopify's iterative-loop rewriting extracts a raw pointer from a recursive
// child field the same way regardless of whether that field is the default
// [std::shared_ptr<T>] representation or (under `Crane Arena`) already a raw
// [T*] -- so codegen need not track, at every extraction site, which
// representation a given field uses.
template <typename T> T *crane_raw(const std::shared_ptr<T> &p) noexcept {
  return p.get();
}

template <typename T> T *crane_raw(T *p) noexcept { return p; }

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

// Unboxes a boxed argument for parameter type [A], unless [A] is itself
// [std::any] — a declared-erased parameter (e.g. a value-dependent domain
// like [domty n]) already receives the boxed value as-is; any_cast-ing an
// [std::any] to [std::any] requires the *contained* value to itself be an
// [std::any] (double-boxed), which is not how erased-domain values are
// represented, and throws [std::bad_any_cast].
template <class A> decltype(auto) crane_erase_fn_unbox(std::any &as) {
  if constexpr (std::is_same_v<A, std::any>) {
    return (as);
  } else {
    return std::any_cast<A>(as);
  }
}

template <class R, class... A>
std::function<std::any(std::conditional_t<true, std::any, A>...)>
crane_erase_fn_impl(std::function<R(A...)> f) {
  return [f = std::move(f)](
             std::conditional_t<true, std::any, A>... as) mutable -> std::any {
    if constexpr (std::is_void_v<R>) {
      f(crane_erase_fn_unbox<A>(as)...);
      return std::any{};
    } else {
      return std::any(f(crane_erase_fn_unbox<A>(as)...));
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

// Detects [std::pair<X, Y>] specializations so [crane_any_cast] can recurse
// into pair components (see below).
template <class T> struct crane_is_pair : std::false_type {};
template <class X, class Y>
struct crane_is_pair<std::pair<X, Y>> : std::true_type {};

// [std::any_cast<T>], generalized to recover a pair [T = std::pair<X, Y>]
// whose components were themselves boxed independently as
// [std::pair<std::any, std::any>] rather than stored directly as a concrete
// [std::pair<X, Y>].
//
// A value-dependent pair/tuple flowing through an erased ([std::any]) slot
// (e.g. a grammar action's tuple-typed result, built up one component at a
// time via nested destructuring whose own component types cannot be
// statically resolved at that construction site — see
// [gen_expr_custom_cons] in translation.ml) is erased ONE COMPONENT AT A
// TIME: each component is stored as plain [std::any], giving
// [std::pair<std::any, std::any>] boxed into the outer [std::any]. A
// consumer that knows the pair's true concrete element type [T] (e.g. from
// a declared record field like [list (string * nat)]) must therefore
// recover it by unboxing each component individually, not by taking a
// direct [std::any_cast<T>] of the whole pair (which throws
// [std::bad_any_cast] because the boxed value is [pair<any,any>], not
// [pair<X,Y>]).
template <class T> T crane_any_cast(const std::any &a) {
  if constexpr (crane_is_pair<T>::value) {
    if (auto *p = std::any_cast<T>(&a)) {
      return *p;
    }
    using X = typename T::first_type;
    using Y = typename T::second_type;
    const auto &boxed = std::any_cast<const std::pair<std::any, std::any> &>(a);
    return T(crane_any_cast<X>(boxed.first), crane_any_cast<Y>(boxed.second));
  } else {
    return std::any_cast<T>(a);
  }
}

// Converts a type-erased sequence container (element type [std::any], e.g. a
// [std::deque<std::any>] produced when a value-dependent list is erased) into a
// concrete-element container [Dst] by [std::any_cast]-ing each element.
//
// This is the container analogue of the element-converting constructor that
// Crane's own [List<A>] carries: [std::deque]/[std::vector] and other mapped
// containers have no such ctor, so an erased list leaf forwarded into a
// consumer whose parameter has a concrete element type (e.g.
// [triples_le_max(const std::deque<rgb>&)]) needs its elements unboxed here.
//
// Each element is either already of the destination element type (passed
// through) or a [std::any] holding it (unboxed with [crane_any_cast], which
// also recovers pair-typed elements whose components were boxed
// independently -- see [crane_any_cast] above).
// Detects a "box-like" element (e.g. immer::box<U>): has a value_type, a
// .get(), and is constructible from its value_type. Used so an erased element
// (std::any holding U or pair<any,any>) is unboxed to U and *re-boxed*, rather
// than any_cast directly to box<U> (which throws).
template <class T, class = void>
struct crane_is_boxlike : std::false_type {};
template <class T>
struct crane_is_boxlike<
    T, std::void_t<typename T::value_type,
                   decltype(std::declval<const T &>().get())>> {
  using U = typename T::value_type;
  static constexpr bool value = std::is_constructible_v<T, U>;
  // A `Boxed Element` wrapper (e.g. immer::box<U>) must convert implicitly
  // both ways -- constructible from U, and convertible back via .get() (or
  // an equivalent `operator const U&()`) -- because Crane's cons/match
  // codegen for boxed elements relies on these conversions happening
  // implicitly rather than emitting explicit wrap/unwrap calls (see
  // ~/crane/WRAP.md section 2.1). A wrapper satisfying `value_type`+`.get()`
  // but failing either direction is misconfigured; fail loudly here instead
  // of producing a confusing error downstream.
  static_assert(
      value &&
          std::is_convertible_v<decltype(std::declval<const T &>().get()), U>,
      "Crane Boxed Element wrapper must convert implicitly both ways to/from "
      "its bare element type: constructible from the element, and its "
      ".get() must convert to the element type.");
};

template <class Dst, class Src> Dst crane_container_cast(Src &&src) {
  using Elt = typename Dst::value_type;
  auto _convert = [](auto &&_e) -> Elt {
    if constexpr (std::is_same_v<std::decay_t<decltype(_e)>, Elt>)
      return _e;
    else if constexpr (crane_is_boxlike<Elt>::value) {
      using U = typename Elt::value_type;
      const std::any &_a = _e; // box<any> -> const any&, or any -> any
      return Elt(crane_any_cast<U>(_a));
    } else
      return crane_any_cast<Elt>(_e);
  };
  // Fast path for containers that build in one shot from a range (e.g. the
  // cons-list crane::list, where repeated push_back would each rebuild the spine
  // and make this O(n^2)): convert into a temp buffer, then a single O(n)
  // from_range construction.
  if constexpr (requires(Elt *_p) { Dst::from_range(_p, _p); }) {
    std::vector<Elt> _tmp;
    for (auto &&_e : src)
      _tmp.push_back(_convert(_e));
    return Dst::from_range(_tmp.begin(), _tmp.end());
  } else {
    Dst dst;
    for (auto &&_e : src) {
      Elt _elt = _convert(_e);
      // Mutable STL-like containers (deque/vector) append in place; immutable
      // persistent containers (e.g. immer::flex_vector) return a new value from
      // push_back, so reassign instead.
      if constexpr (requires(Dst d, Elt v) { d.insert(d.end(), v); }) {
        dst.insert(dst.end(), std::move(_elt));
      } else {
        dst = std::move(dst).push_back(std::move(_elt));
      }
    }
    return dst;
  }
}
