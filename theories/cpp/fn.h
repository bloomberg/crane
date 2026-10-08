// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::fn<R(A...)> -- a closure as a shared, immutable value.
//
// A Rocq function value is immutable, and copying one should copy a pointer,
// as it does in OCaml.  [std::function] owns its callable instead: a copy
// clones the closure and, recursively, every closure it captured, which made
// continuation-heavy code (an interaction tree's [bind]) spend most of its
// time allocating.  An [fn] is one pointer to a heap block holding a count, an
// entry point and the callable; a copy bumps the count and nothing is ever
// cloned.
//
// Sharing is sound only because the callable cannot change: the block stores
// it [const] and [operator()] is [const], so a closure body that moves out of
// its own captures -- which would leave the next call, from any copy, reading
// a moved-from value -- does not compile.  Only a callable that can be called
// through a [const] reference converts to an [fn].
//
// The block is a [shared_block], counted under the policy shared_block.h
// describes.
//
// Compile every translation unit with CRANE_FN_STATS to count blocks made,
// copies shared, calls and frees; the totals are written to stderr at exit.
#pragma once
#include <cstddef>
#include <functional>
#include <new>
#include <type_traits>
#include <utility>
#include "pool.h"
#include "shared_block.h"
#ifdef CRANE_FN_STATS
#include <cstdio>
#endif

namespace crane {

#ifdef CRANE_FN_STATS
struct fn_stats_t {
  unsigned long long made = 0;   // blocks allocated
  unsigned long long shared = 0; // copies that bumped a count
  unsigned long long calls = 0;
  unsigned long long freed = 0;
  ~fn_stats_t() {
    std::fprintf(stderr, "crane::fn: made=%llu shared=%llu calls=%llu freed=%llu\n",
                 made, shared, calls, freed);
  }
};
inline fn_stats_t &fn_stats() noexcept {
  static fn_stats_t s;
  return s;
}
#define CRANE_FN_STAT(field) (++::crane::fn_stats().field)
#else
#define CRANE_FN_STAT(field) ((void)0)
#endif

CRANE_RC_POLICY_BEGIN

template <class Sig> class fn;

namespace fn_detail {

// The entry for a saturated application of a curried function, [f(a)(b)]
// for an [f] whose result is itself an [fn]: a callable written as one
// lambda returning another -- a state monad's continuation -- runs the inner
// one where it is made, never boxing it into the [fn] the one-argument entry
// must return.  OCaml compiles [fun a s -> ...] to a closure of arity two for
// the same reason.  Present only for that shape.
template <class R, class... A> struct curried_entry {};
template <class R2, class B, class A> struct curried_entry<fn<R2(B)>, A> {
  using result2 = R2;
  using arg2 = B;
  R2 (*const invoke2)(const void *, const A &, const B &);
};

// What every block of one signature starts with.  The entry points are
// function pointers rather than a vtable so the header is three words and
// the callable follows it directly.
//
// There are two ways in.  [invoke] takes arguments the caller hands over,
// to be moved into the callable's parameters.  [invoke_ref] takes arguments
// the caller keeps, by [const &]: a callable whose parameters are [const &]
// reads them where they are, and one that takes them by value copies them
// once, in its own parameter.  Through a single by-value entry every
// argument the caller kept -- a field of a node, a loop's state -- was
// copied at the call whatever the callable did with it.
template <class R, class... A>
struct block : shared_block, curried_entry<R, A...> {
  R (*const invoke)(const block *, A &&...);
  R (*const invoke_ref)(const block *, const A &...);
};

// [std::invoke_r], which is C++23; the BDE flavour compiles as C++20.
template <class R, class F, class... A> R invoke_as(F &&f, A &&...a) {
  if constexpr (std::is_void_v<R>)
    std::invoke(std::forward<F>(f), std::forward<A>(a)...);
  else
    return std::invoke(std::forward<F>(f), std::forward<A>(a)...);
}

template <class F, class R, class... A>
struct holder : block<R, A...>,
                pool_detail::pooled<holder<F, R, A...>> {
  const F f;

  template <class G>
  explicit holder(G &&g)
      : block<R, A...>{{{}, &drop}, curried(), &call, &call_ref},
        f(std::forward<G>(g)) {}

  static constexpr curried_entry<R, A...> curried() {
    if constexpr (std::is_empty_v<curried_entry<R, A...>>)
      return {};
    else
      return {&call2<>};
  }
  // [f(a)(b)], the inner callable left as [f] made it.
  template <class E = curried_entry<R, A...>>
  static typename E::result2 call2(const void *b, const A &...a,
                                   const typename E::arg2 &x) {
    const F &f =
        static_cast<const holder *>(static_cast<const block<R, A...> *>(b))->f;
    return invoke_as<typename E::result2>(std::invoke(f, a...), x);
  }

  static R call(const block<R, A...> *b, A &&...a) {
    return invoke_as<R>(static_cast<const holder *>(b)->f,
                        std::forward<A>(a)...);
  }
  static R call_ref(const block<R, A...> *b, const A &...a) {
    const F &f = static_cast<const holder *>(b)->f;
    if constexpr (std::is_invocable_r_v<R, const F &, const A &...>)
      return invoke_as<R>(f, a...);
    else
      // A parameter that wants a mutable argument gets its own copy.
      return invoke_as<R>(f, A(a)...);
  }
  static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
    CRANE_FN_STAT(freed);
    holder::dispose(static_cast<const holder *>(static_cast<const shared_block *>(b)), h);
  }
};

// The signature a callable's own [operator()] states, for the deduction
// guide: the same rule [std::function]'s guide follows.
template <class M> struct sig_of {};
template <class R, class G, class... A>
struct sig_of<R (G::*)(A...) const> { using type = R(A...); };
template <class R, class G, class... A>
struct sig_of<R (G::*)(A...) const &> { using type = R(A...); };
template <class R, class G, class... A>
struct sig_of<R (G::*)(A...) const noexcept> { using type = R(A...); };
template <class R, class G, class... A>
struct sig_of<R (G::*)(A...) const & noexcept> { using type = R(A...); };
template <class R, class G, class... A>
struct sig_of<R (G::*)(A...)> { using type = R(A...); };
template <class R, class G, class... A>
struct sig_of<R (G::*)(A...) noexcept> { using type = R(A...); };

template <class T> struct is_std_function : std::false_type {};
template <class Sig>
struct is_std_function<std::function<Sig>> : std::true_type {};

} // namespace fn_detail

template <class Sig> class fn;

template <class R, class... A> class fn<R(A...)> {
  using block = fn_detail::block<R, A...>;
  const block *p_ = nullptr;

public:
  // A copy is a refcount bump (see field.h).
  using crane_cheap_copy = void;

private:
  void retain() const noexcept {
    if (p_) {
      p_->retain();
      CRANE_FN_STAT(shared);
    }
  }
  void release() const noexcept {
    if (p_)
      p_->release();
  }

public:
  using result_type = R;

  fn() noexcept = default;
  fn(std::nullptr_t) noexcept {}

  // Any callable that can be called through a [const] reference with these
  // arguments, and whose result converts to [R]: the same set
  // [std::function] accepts, less the callables that mutate themselves.
  //
  // Separate conjuncts, checked in order: a type that is not callable at all
  // stops at the second, before its copy constructor is asked about -- which
  // for a type holding an [fn] would be the question being answered.
  template <class F, class D = std::decay_t<F>>
    requires(!std::is_same_v<D, fn>) &&
            (std::is_invocable_r_v<R, const D &, A...>) &&
            (std::is_copy_constructible_v<D>)
  fn(F &&f) {
    // A null function pointer, or an empty [std::function], is an empty
    // [fn], as [std::function] has it.
    if constexpr (std::is_pointer_v<D> || std::is_member_pointer_v<D> ||
                  fn_detail::is_std_function<D>::value)
      if (!f)
        return;
    p_ = new fn_detail::holder<D, R, A...>(std::forward<F>(f));
    CRANE_FN_STAT(made);
  }

  fn(const fn &o) noexcept : p_(o.p_) { retain(); }
  fn(fn &&o) noexcept : p_(std::exchange(o.p_, nullptr)) {}
  // [o] may be owned by the closure this one releases, so its pointer is
  // read before anything is released.
  fn &operator=(const fn &o) noexcept {
    fn copy(o);
    swap(copy);
    return *this;
  }
  fn &operator=(fn &&o) noexcept {
    fn taken(std::move(o));
    swap(taken);
    return *this;
  }
  fn &operator=(std::nullptr_t) noexcept {
    release();
    p_ = nullptr;
    return *this;
  }
  ~fn() { release(); }

  // [crane::release_into]: the closure released into [h], this one empty.
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (p_) p_->release_into(h);
    p_ = nullptr;
  }

  // Arguments the caller keeps go in by reference; arguments it gives up
  // are moved.  Where a parameter type is itself a reference the two
  // coincide, and only the first exists.
  R operator()(const A &...a) const {
    if (!p_)
      throw std::bad_function_call();
    CRANE_FN_STAT(calls);
    return p_->invoke_ref(p_, a...);
  }
  R operator()(A &&...a) const
    requires((!std::is_reference_v<A>) && ...) && (sizeof...(A) > 0)
  {
    if (!p_)
      throw std::bad_function_call();
    CRANE_FN_STAT(calls);
    return p_->invoke(p_, std::forward<A>(a)...);
  }

  template <class R2, class B, class A0>
  friend R2 apply2(const fn<fn<R2(B)>(A0)> &f, const std::type_identity_t<A0> &a,
                   const std::type_identity_t<B> &b);

  explicit operator bool() const noexcept { return p_ != nullptr; }
  friend bool operator==(const fn &f, std::nullptr_t) noexcept {
    return f.p_ == nullptr;
  }
  void swap(fn &o) noexcept { std::swap(p_, o.p_); }
};

// [f(a)(b)].  Through an [fn] whose result is an [fn], by the entry that
// leaves the intermediate callable unboxed; anything else is applied twice.
namespace fn_detail {
template <class F> struct is_curried_fn : std::false_type {};
template <class R2, class B, class A0>
struct is_curried_fn<fn<fn<R2(B)>(A0)>> : std::true_type {};
} // namespace fn_detail

template <class F, class X, class Y>
  requires(!fn_detail::is_curried_fn<F>::value)
decltype(auto) apply2(const F &f, X &&a, Y &&b) {
  return f(std::forward<X>(a))(std::forward<Y>(b));
}
template <class R2, class B, class A0>
R2 apply2(const fn<fn<R2(B)>(A0)> &f, const std::type_identity_t<A0> &a,
          const std::type_identity_t<B> &b) {
  if (!f.p_)
    throw std::bad_function_call();
  CRANE_FN_STAT(calls);
  return f.p_->invoke2(f.p_, a, b);
}

template <class R, class... A> fn(R (*)(A...)) -> fn<R(A...)>;
template <class F>
fn(F) -> fn<typename fn_detail::sig_of<decltype(&F::operator())>::type>;

CRANE_RC_POLICY_END

// Whether [T] is some [fn<...>]: the [std::function]-shaped type generated
// code writes for a function type.
template <class T> struct is_fn : std::false_type {};
template <class Sig> struct is_fn<fn<Sig>> : std::true_type {};

} // namespace crane
