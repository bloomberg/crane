// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Runtime helper for storing a concrete callable into a type-erased
// [crane::obj] field.
#pragma once
#include "obj.h"
#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>
#include "fn.h"
//
// When a value-dependent function type is erased to [crane::obj], the
// application site reads the callable back with
// [crane::any_cast<crane::fn<crane::obj(crane::obj...)>>], so the construction
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

// Declared here, defined below: the generic-lambda branch of
// [crane_erase_fn] needs it to recover a concrete result from a callable
// whose own result is boxed.
template <class T> T crane_any_cast(const crane::obj &a);
template <class Dst, class Src> Dst crane_convert(Src &&src);

// [crane_erase_fn] adapts an arbitrary callable to
// [crane::fn<crane::obj(crane::obj...)>] and boxes the result into [crane::obj].
// Two cases:
//
//   * Concrete-signature callables (a named function, a monomorphic lambda,
//     etc.): [crane::fn] CTAD deduces the signature [R(A...)], and the
//     adapter unboxes each argument with [crane::any_cast<A>].
//
//   * Generic lambdas (e.g. [ [](const auto&){...} ], produced when a function's
//     domain is a value-dependent/abstract type erased to [crane::obj]): CTAD
//     cannot deduce a signature, so the callable is wrapped as a unary
//     [any -> any] adapter that forwards the boxed argument directly (a generic
//     lambda accepts the [crane::obj] as its [const auto&] parameter).
//
// Emitted as a global (like [ITree] in crane_itree.h) rather than in
// [namespace crane] so the extractor can reference it with a plain identifier.

// Unboxes a boxed argument for parameter type [A], unless [A] is itself
// [crane::obj] — a declared-erased parameter (e.g. a value-dependent domain
// like [domty n]) already receives the boxed value as-is; any_cast-ing an
// [crane::obj] to [crane::obj] requires the *contained* value to itself be an
// [crane::obj] (double-boxed), which is not how erased-domain values are
// represented, and throws [std::bad_any_cast].
template <class A> decltype(auto) crane_erase_fn_unbox(crane::obj &as) {
  // [A] is taken from the callable's own signature, so it may be a reference
  // or const-qualified ([const crane::obj&] for a lambda that declares its
  // erased parameter by reference); the question is about the underlying
  // type.
  if constexpr (std::is_same_v<std::remove_cvref_t<A>, crane::obj>) {
    return (as);
  } else {
    // Tolerantly: a generated inductive is boxed at its all-[crane::obj]
    // instantiation (see [crane_convert]), and read here at the one the
    // callable declares.
    return crane_any_cast<std::remove_cvref_t<A>>(as);
  }
}

// The value a callable returning [void] -- a Rocq [unit] -- yields at [Ret].
// Erased, unit is boxed as [std::monostate], which is what a consumer opens;
// an empty [crane::obj] would hold nothing to open.
template <class Ret> Ret crane_unit_as() {
  if constexpr (std::is_same_v<Ret, crane::obj>)
    return crane::obj(std::monostate{});
  else
    return Ret{};
}

// [Ret] is the result type of the adapted callable: [crane::obj] when the
// consumer erases the result too, or a concrete type when only the arguments
// are erased (e.g. a higher-kinded class method taking
// [crane::fn<typename I::M(crane::obj)>]).  The signature [R(A...)] arrives as a
// tag, so the callable itself is captured as it is rather than first wrapped
// in an [fn] of its own.
template <class Ret, class R, class... A, class F>
crane::fn<Ret(std::conditional_t<true, crane::obj, A>...)>
crane_erase_fn_impl(crane::fn<R(A...)> *, F &&f) {
  return [f = std::forward<F>(f)](
             std::conditional_t<true, crane::obj, A>... as) -> Ret {
    if constexpr (std::is_void_v<R>) {
      f(crane_erase_fn_unbox<A>(as)...);
      return crane_unit_as<Ret>();
    } else {
      return crane_convert<Ret>(f(crane_erase_fn_unbox<A>(as)...));
    }
  };
}

template <class Ret = crane::obj, class F> auto crane_erase_fn(F &&f) {
  if constexpr (requires { crane::fn{f}; }) {
    return crane_erase_fn_impl<Ret>(
        static_cast<decltype(crane::fn{f}) *>(nullptr), std::forward<F>(f));
  } else if constexpr (!requires { f(std::declval<crane::obj>()); }) {
    // Not callable at all: the value only *might* have been a function
    // (its Rocq type was a variable), so there is nothing to erase.
    return std::forward<F>(f);
  } else {
    return crane::fn<Ret(crane::obj)>(
        [f = std::forward<F>(f)](crane::obj a) -> Ret {
          if constexpr (std::is_void_v<decltype(f(a))>) {
            f(a);
            return crane_unit_as<Ret>();
          } else if constexpr (std::is_same_v<std::decay_t<decltype(f(a))>,
                                              crane::obj>) {
            // A generic lambda over an erased domain hands back whatever it
            // was given, still boxed; a slot that kept a concrete result
            // ([crane::fn<uint64_t(crane::obj)>]) needs it unboxed, not
            // converted.
            return crane_any_cast<Ret>(f(a));
          } else {
            return Ret(f(a));
          }
        });
  }
}

// [crane_erase_fn<Ret>(F)] for a global -- a function, or a constant -- made
// once and shared: the adapter of a value that never changes is itself one,
// and building it at every use cost an allocation each time a subevent was
// injected.  Per thread, as the [fn]'s count may not be atomic; and never
// freed, so that no thread's exit runs after the heap it came from.
template <auto &F, class Ret = crane::obj> const auto &crane_erase_global() {
  static thread_local const auto *f = new auto(crane_erase_fn<Ret>(F));
  return *f;
}

// Runtime helper for calling a genuinely-concrete callable [f] with
// arguments that may be boxed as [crane::obj] even though [f] does not accept
// [crane::obj] directly.
//
// This arises when a value-dependent parameter (e.g. a functor's abstract
// [S.sem a]) is destructured from a type-erased carrier (a [std::pair<any,
// any>] built for a generic domain), so the resulting value is statically
// [crane::obj] at the call site.  The callee [f], however, is only concrete at
// C++ template instantiation time (e.g. a functor parameter deduced from a
// caller-supplied lambda with a concrete signature like
// [bool(std::string, std::string)]).  Crane cannot know at OCaml translation
// time whether [f] will end up generic (accepts [crane::obj] as-is) or
// concrete (needs each boxed argument unwrapped with
// [crane::any_cast<ParamType>]), so the decision is deferred to C++ via
// [crane::fn] CTAD, same trick as [crane_erase_fn].
template <class Sig, std::size_t I> struct crane_fn_param;
template <class R, class... P, std::size_t I>
struct crane_fn_param<crane::fn<R(P...)>, I> {
  using type = std::tuple_element_t<I, std::tuple<P...>>;
};

template <class Sig, std::size_t I, class A>
decltype(auto) crane_call_erased_unbox(A &&a) {
  using T = typename crane_fn_param<Sig, I>::type;
  if constexpr (std::is_same_v<std::decay_t<A>, crane::obj> &&
                !std::is_same_v<std::decay_t<T>, crane::obj>) {
    return crane::any_cast<T>(std::forward<A>(a));
  } else {
    return std::forward<A>(a);
  }
}

template <class F, class... Args, std::size_t... I>
decltype(auto) crane_call_erased_dispatch(std::index_sequence<I...>, F &&f,
                                           Args &&...args) {
  using Sig = decltype(crane::fn{f});
  return f(crane_call_erased_unbox<Sig, I>(std::forward<Args>(args))...);
}

template <class F, class... Args>
decltype(auto) crane_call_erased(F &&f, Args &&...args) {
  if constexpr (requires { crane::fn{f}; }) {
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

// [T] with every type argument [crane::obj]: the instantiation code that
// erases a type's parameters builds its values at.  Only for a generated
// inductive -- a [variant_t] carrier, which converts from any instantiation of
// itself -- since respelling an arbitrary template's arguments need not name a
// valid type ([std::vector<X, std::allocator<X>>]).
template <class T> struct crane_all_any {};
template <template <class...> class C, class... A>
  requires requires { typename C<A...>::variant_t; }
struct crane_all_any<C<A...>> {
  using type = C<std::conditional_t<true, crane::obj, A>...>;
};

// [crane::any_cast<T>], generalized to recover a pair [T = std::pair<X, Y>]
// whose components were themselves boxed independently as
// [std::pair<crane::obj, crane::obj>] rather than stored directly as a concrete
// [std::pair<X, Y>].
//
// A value-dependent pair/tuple flowing through an erased ([crane::obj]) slot
// (e.g. a grammar action's tuple-typed result, built up one component at a
// time via nested destructuring whose own component types cannot be
// statically resolved at that construction site — see
// [gen_expr_custom_cons] in translation.ml) is erased ONE COMPONENT AT A
// TIME: each component is stored as plain [crane::obj], giving
// [std::pair<crane::obj, crane::obj>] boxed into the outer [crane::obj]. A
// consumer that knows the pair's true concrete element type [T] (e.g. from
// a declared record field like [list (string * nat)]) must therefore
// recover it by unboxing each component individually, not by taking a
// direct [crane::any_cast<T>] of the whole pair (which throws
// [std::bad_any_cast] because the boxed value is [pair<any,any>], not
// [pair<X,Y>]).
template <class T> T crane_any_cast(const crane::obj &a) {
  if constexpr (std::is_same_v<T, crane::obj>) {
    // The target may be a dependent associated type that resolves to
    // [crane::obj] itself (a type-class instance with a fully erased carrier).
    // Casting [any] to [any] is the identity, not an unwrap.
    return a;
  } else if constexpr (crane_is_pair<T>::value) {
    if (auto *p = crane::any_cast<T>(&a)) {
      return *p;
    }
    using X = typename T::first_type;
    using Y = typename T::second_type;
    const auto &boxed = crane::any_cast<const std::pair<crane::obj, crane::obj> &>(a);
    return T(crane_any_cast<X>(boxed.first), crane_any_cast<Y>(boxed.second));
  } else {
    // A value built where the type's parameters were erased -- a category
    // over families at [obj := Type -> Type] builds [Sum1<any, any, any>] --
    // is read at the instantiation the position states, through the
    // converting constructor.
    if constexpr (requires { typename crane_all_any<T>::type; }) {
      using E = typename crane_all_any<T>::type;
      if constexpr (!std::is_same_v<E, T> &&
                    std::is_constructible_v<T, const E &>) {
        if (auto *p = crane::any_cast<E>(&a)) {
          return T(*p);
        }
      }
    }
    return crane::any_cast<T>(a);
  }
}

// Converts a type-erased sequence container (element type [crane::obj], e.g. a
// [std::deque<crane::obj>] produced when a value-dependent list is erased) into a
// concrete-element container [Dst] by [crane::any_cast]-ing each element.
//
// This is the container analogue of the element-converting constructor that
// Crane's own [List<A>] carries: [std::deque]/[std::vector] and other mapped
// containers have no such ctor, so an erased list leaf forwarded into a
// consumer whose parameter has a concrete element type (e.g.
// [triples_le_max(const std::deque<rgb>&)]) needs its elements unboxed here.
//
// Each element is either already of the destination element type (passed
// through) or a [crane::obj] holding it (unboxed with [crane_any_cast], which
// also recovers pair-typed elements whose components were boxed
// independently -- see [crane_any_cast] above).
// Detects a "box-like" element (e.g. immer::box<U>): has a value_type, a
// .get(), and is constructible from its value_type. Used so an erased element
// (crane::obj holding U or pair<any,any>) is unboxed to U and *re-boxed*, rather
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

// The hook a carrier that is not a container uses to say how it is read at
// another element type.  A [std::shared_ptr<ITree<A>>] is the case that needs
// it: the element type is real but there is nothing to walk, so the carrier
// itself has to supply the conversion.  Found by argument-dependent lookup on
// the tag, so a header that defines a carrier declares it alongside, and this
// one need not know the carrier exists.
template <class T> struct crane_tag {};

template <class Dst, class Src> Dst crane_container_cast_impl(Src &&src) {
  using Elt = typename Dst::value_type;
  auto _convert = [](auto &&_e) -> Elt {
    if constexpr (std::is_same_v<std::decay_t<decltype(_e)>, Elt>)
      return _e;
    // The other direction: a concrete element going INTO an erased carrier
    // ([std::optional<Nat>] handed to a dictionary method declared over
    // [std::optional<crane::obj>]).  Boxing is the conversion; nothing is cast
    // out.
    else if constexpr (std::is_same_v<Elt, crane::obj>)
      return crane::obj(_e);
    else if constexpr (crane_is_boxlike<Elt>::value) {
      using U = typename Elt::value_type;
      const crane::obj &_a = _e; // box<any> -> const any&, or any -> any
      return Elt(crane_any_cast<U>(_a));
    } else
      return crane_any_cast<Elt>(_e);
  };
  // A carrier holding at most one element (std::optional) is not a range, so
  // no walk reaches its element: convert the contained value, if any.
  if constexpr (!requires(Src &_s) { _s.begin(); } &&
                requires(const Src &_s) {
                  _s.has_value();
                  *_s;
                }) {
    if (!src.has_value())
      return Dst();
    return Dst(_convert(*src));
  } else
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

template <class Dst, class Src> Dst crane_container_cast(Src &&src) {
  // Reading a carrier at the element type it already has is the identity, and
  // saying so here is what makes the cast usable on a carrier that is not a
  // container: [Box<crane::obj>] has neither [value_type] nor [begin], so the
  // walk below would not compile even though there is nothing to walk.  The
  // same shortcut [crane_convert] takes, for the same reason.
  if constexpr (std::is_same_v<Dst, std::remove_cvref_t<Src>>)
    return std::forward<Src>(src);
  else if constexpr (requires {
                  crane_cast_to(crane_tag<Dst>{}, std::forward<Src>(src));
                })
    return crane_cast_to(crane_tag<Dst>{}, std::forward<Src>(src));
  // The carrier already knows how to be read at the other element type: a
  // converting constructor, or a conversion function on an aggregate that
  // cannot have one.  That answer is exact, and it is the only one for a
  // carrier that is not a container -- the element walk below needs a
  // [value_type] that a record carrier does not have.
  //
  // Only where there is no element walk.  A container that has one already
  // reaches its elements through it, and the two routes can disagree on the
  // *value* rather than on whether they compile, so this must not move in
  // front of a route that works today.
  else if constexpr (!requires { typename Dst::value_type; } &&
                     std::is_constructible_v<Dst, Src>)
    return Dst(std::forward<Src>(src));
  else
    return crane_container_cast_impl<Dst>(std::forward<Src>(src));
}

// The routes [crane_convert<Dst>] has from [Src], in the order it tries them.
// One function decides, and both the conversion and the question of whether
// there is one read its answer, so the two cannot drift apart.
enum class crane_route { identity, unbox, box_all_any, hook, construct, walk, none };

template <class Dst, class Src> consteval crane_route crane_convert_route() {
  using S = std::remove_cvref_t<Src>;
  if constexpr (std::is_same_v<Dst, S>)
    return crane_route::identity;
  else if constexpr (std::is_same_v<S, crane::obj>)
    return crane_route::unbox;
  // Into a box, a generated inductive goes at the instantiation code that
  // erased its parameters reads it at -- the all-[crane::obj] one (see
  // [crane_all_any]) -- and a reader at a concrete instantiation recovers it
  // through [crane_any_cast]'s fallback.  A nested event [Sum1<BE, CE, X>]
  // inside an event already boxed at [Sum1<any, any, any>] is read by the
  // inner [case_] at the same shape.
  else if constexpr (std::is_same_v<Dst, crane::obj> &&
                     requires { typename crane_all_any<S>::type; })
    return crane_route::box_all_any;
  else if constexpr (requires(Src &&s) {
                       crane_cast_to(crane_tag<Dst>{}, std::forward<Src>(s));
                     })
    return crane_route::hook;
  else if constexpr (std::is_constructible_v<Dst, Src>)
    return crane_route::construct;
  else if constexpr (requires { typename Dst::value_type; })
    return crane_route::walk;
  else
    return crane_route::none;
}

// Whether [crane_convert<Dst>] has a route from [Src].  A generated
// converting constructor asks this before converting, because it is written
// for every field of every constructor and only the source's own constructor
// is ever reached -- a field of some other one may have no route at all, and
// saying so is not an error.
template <class Dst, class Src>
concept crane_convertible = crane_convert_route<Dst, Src>() != crane_route::none;

// A value reaching a slot spelled at another instantiation of its own type.
// Conversion is the ordinary answer; a carrier that cannot be constructed
// from itself at another element type answers through [crane_cast_to].
template <class Dst, class Src> Dst crane_convert(Src &&src) {
  constexpr crane_route route = crane_convert_route<Dst, Src>();
  if constexpr (route == crane_route::identity)
    return std::forward<Src>(src);
  else if constexpr (route == crane_route::unbox)
    return crane_any_cast<Dst>(src);
  else if constexpr (route == crane_route::box_all_any) {
    using S = std::remove_cvref_t<Src>;
    using E = typename crane_all_any<S>::type;
    if constexpr (!std::is_same_v<E, S> && std::is_constructible_v<E, const S &>)
      return crane::obj(E(src));
    else
      return crane::obj(std::forward<Src>(src));
  } else if constexpr (route == crane_route::hook)
    return crane_cast_to(crane_tag<Dst>{}, std::forward<Src>(src));
  else if constexpr (route == crane_route::construct)
    return Dst(std::forward<Src>(src));
  else if constexpr (route == crane_route::walk)
    return crane_container_cast_impl<Dst>(std::forward<Src>(src));
  else
    // No route: let the conversion itself be the diagnostic, rather than a
    // failure inside machinery the reader did not write.
    return Dst(std::forward<Src>(src));
}

// A composite carrier -- a Rocq carrier of the shape [fun T => (T * box T)] --
// is neither a range nor constructible from itself at another element type,
// because [std::pair]'s converting constructor asks each component to be
// constructible and an erased component needs a cast instead.  It is still
// read component-wise, so say that once here rather than special-casing pairs
// in the machinery above: this is the [crane_cast_to] hook a carrier uses to
// declare how it is read, and it is found by argument-dependent lookup.
template <class A, class B, class X, class Y>
std::pair<A, B> crane_cast_to(crane_tag<std::pair<A, B>>,
                              const std::pair<X, Y> &src) {
  return std::pair<A, B>(crane_convert<A>(src.first),
                         crane_convert<B>(src.second));
}

// [std::optional] is the opposite problem and needs the same hook.  It is
// constructible from an optional at another element type -- too readily:
// [std::optional<crane::obj>] takes a [std::optional<Nat>] through its
// value constructor, since [crane::obj] holds anything, and stores the whole
// optional in the box where the consumer expects the [Nat].  Say how it is
// really read, which is through the contained value if there is one.
template <class A, class X>
std::optional<A> crane_cast_to(crane_tag<std::optional<A>>,
                               const std::optional<X> &src) {
  if (!src.has_value())
    return std::optional<A>();
  return std::optional<A>(crane_convert<A>(*src));
}

// A function at another result type -- a continuation built where the
// result was erased, [crane::fn<Itree<crane::obj, crane::obj>(crane::obj)>],
// stored where it is [crane::fn<Itree<E, R>(crane::obj)>] -- is read by
// reading what it returns.  The arguments are the same, so only the result
// is converted.
template <class R, class... A, class S>
crane::fn<R(A...)> crane_cast_to(crane_tag<crane::fn<R(A...)>>,
                                 const crane::fn<S(A...)> &src) {
  return [src](A... a) -> R {
    return crane_convert<R>(src(std::forward<A>(a)...));
  };
}
