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
// The count is non-atomic when the generated header defines
// CRANE_NON_ATOMIC_RC (the [Crane NonAtomicRc] policy, withheld from units
// that spawn threads), and atomic otherwise.  The two layouts live in
// different inline namespaces, so a program that mixes them fails to link
// rather than sharing a block between the two disciplines.
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
#ifndef CRANE_NON_ATOMIC_RC
#include <atomic>
#endif
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

#ifdef CRANE_NON_ATOMIC_RC
inline namespace fn_local {
#else
inline namespace fn_shared {
#endif

namespace fn_detail {

#ifdef CRANE_NON_ATOMIC_RC
struct count {
  std::size_t n{1};
  void inc() noexcept { ++n; }
  bool dec() noexcept { return --n == 0; }
  bool sole() const noexcept { return n == 1; }
};
#else
struct count {
  std::atomic<std::size_t> n{1};
  void inc() noexcept { n.fetch_add(1, std::memory_order_relaxed); }
  bool dec() noexcept { return n.fetch_sub(1, std::memory_order_acq_rel) == 1; }
  bool sole() const noexcept { return n.load(std::memory_order_acquire) == 1; }
};
#endif

// Frees a block whose count reached zero without recursing into what it
// held.  A block's destructor releases what it captured, which may free
// another block, and so on down a chain as long as the program's longest
// continuation or tree: freed recursively, that is one C++ frame per link.
// Instead a free that happens while another is running is queued, and the
// outermost one drains the queue.
struct pending_free {
  const void *block;
  void (*destroy)(const void *) noexcept;
};
//
// The queue has no destructor: a value in a static is freed after the
// thread's own thread_local objects are gone, so the queue must still work
// then.  Its buffer lives as long as the thread.
struct free_queue {
  bool draining = false;
  pending_free *items = nullptr;
  std::size_t size = 0, cap = 0;
  void push(pending_free f) {
    if (size == cap) {
      std::size_t ncap = cap ? cap * 2 : 64;
      auto *n = static_cast<pending_free *>(
          ::operator new(ncap * sizeof(pending_free)));
      for (std::size_t i = 0; i < size; ++i)
        n[i] = items[i];
      ::operator delete(items);
      items = n;
      cap = ncap;
    }
    items[size++] = f;
  }
};
inline free_queue &frees() noexcept {
  static constinit thread_local free_queue q;
  return q;
}
inline void free_block(const void *block,
                       void (*destroy)(const void *) noexcept) noexcept {
  free_queue &q = frees();
  if (q.draining) {
    q.push({block, destroy});
    return;
  }
  q.draining = true;
  destroy(block);
  while (q.size != 0) {
    pending_free f = q.items[--q.size];
    f.destroy(f.block);
  }
  q.draining = false;
}

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
template <class R, class... A> struct block {
  mutable count rc;
  R (*const invoke)(const block *, A &&...);
  R (*const invoke_ref)(const block *, const A &...);
  void (*const destroy)(const void *) noexcept;
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
      : block<R, A...>{{}, &call, &call_ref, &drop}, f(std::forward<G>(g)) {}

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
  static void drop(const void *b) noexcept {
    delete static_cast<const holder *>(static_cast<const block<R, A...> *>(b));
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

  void retain() const noexcept {
    if (p_) {
      p_->rc.inc();
      CRANE_FN_STAT(shared);
    }
  }
  void release() const noexcept {
    if (p_ && p_->rc.dec()) {
      CRANE_FN_STAT(freed);
      fn_detail::free_block(p_, p_->destroy);
    }
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

  explicit operator bool() const noexcept { return p_ != nullptr; }
  friend bool operator==(const fn &f, std::nullptr_t) noexcept {
    return f.p_ == nullptr;
  }
  void swap(fn &o) noexcept { std::swap(p_, o.p_); }
};

template <class R, class... A> fn(R (*)(A...)) -> fn<R(A...)>;
template <class F>
fn(F) -> fn<typename fn_detail::sig_of<decltype(&F::operator())>::type>;

} // inline namespace

// Whether [T] is some [fn<...>]: the [std::function]-shaped type generated
// code writes for a function type.
template <class T> struct is_fn : std::false_type {};
template <class Sig> struct is_fn<fn<Sig>> : std::true_type {};

} // namespace crane
