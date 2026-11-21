// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The header every shared runtime block starts with: a reference count and
// the function that destroys the block.  A closure ([crane::fn]), an erased
// value's box ([crane::obj]) and a coinductive's cell ([crane::lazy]) are all
// one such block followed by what they hold.
//
// The count is non-atomic when the generated header defines
// CRANE_NON_ATOMIC_RC (the [Crane NonAtomicRc] policy, withheld from units
// that spawn threads), and atomic otherwise.  Every type whose layout holds a
// count is declared inside CRANE_RC_POLICY_BEGIN / CRANE_RC_POLICY_END, an
// inline namespace named after the policy, so the two disciplines are
// different types: a program that passes a block from a unit compiled under
// one policy to a unit compiled under the other fails to link instead of
// sharing a count between them.
//
// Within one translation unit the policy is whichever the first runtime
// header saw.  A unit that runs on several threads (it starts them, or uses
// transactional memory) checks [crane::rc_is_atomic] after its includes, so a
// non-atomic header included ahead of it is a compile error rather than a
// race.
#pragma once
#include <concepts>
#include <cstddef>
#include <new>
#include <type_traits>
#include <utility>
#include "pool.h"
#include "stats.h"
#ifndef CRANE_NON_ATOMIC_RC
#include <atomic>
#endif

// The heap policy (pool.h) is part of the name too: a block's class inherits
// its heap's [pooled].
#if defined(CRANE_NON_ATOMIC_RC) && defined(CRANE_SINGLE_THREADED)
#define CRANE_RC_POLICY_BEGIN inline namespace rc_local_single {
#elif defined(CRANE_NON_ATOMIC_RC)
#define CRANE_RC_POLICY_BEGIN inline namespace rc_local {
#elif defined(CRANE_SINGLE_THREADED)
#define CRANE_RC_POLICY_BEGIN inline namespace rc_shared_single {
#else
#define CRANE_RC_POLICY_BEGIN inline namespace rc_shared {
#endif
#define CRANE_RC_POLICY_END }

namespace crane {

#ifdef CRANE_NON_ATOMIC_RC
inline constexpr bool rc_is_atomic = false;
#else
inline constexpr bool rc_is_atomic = true;
#endif

CRANE_RC_POLICY_BEGIN

namespace block_detail {

// A count at [immortal] is never changed, so its block is never freed and
// no thread writes it: a constant ([crane::constant]) is read from every
// thread, non-atomic counts or not.
inline constexpr std::size_t immortal = ~std::size_t{0};

#ifdef CRANE_NON_ATOMIC_RC
struct count {
  std::size_t n{1};
  void inc() noexcept {
    if (n != immortal) ++n;
  }
  bool dec() noexcept { return n != immortal && --n == 0; }
  bool sole() const noexcept { return n == 1; }
  bool is_immortal() const noexcept { return n == immortal; }
  void make_immortal() noexcept { n = immortal; }
};
#else
struct count {
  std::atomic<std::size_t> n{1};
  void inc() noexcept {
    if (n.load(std::memory_order_relaxed) != immortal) n.fetch_add(1, std::memory_order_relaxed);
  }
  bool dec() noexcept {
    return n.load(std::memory_order_relaxed) != immortal
           && n.fetch_sub(1, std::memory_order_acq_rel) == 1;
  }
  bool sole() const noexcept { return n.load(std::memory_order_acquire) == 1; }
  bool is_immortal() const noexcept { return n.load(std::memory_order_relaxed) == immortal; }
  void make_immortal() noexcept { n.store(immortal, std::memory_order_relaxed); }
};
#endif

// Frees a block whose count reached zero.  A block's destructor releases what
// it held, which may free another block, and so on down a chain as long as
// the program's longest continuation or tree: freed recursively, that is one
// C++ frame per link.  So a free runs at once only a bounded number of frames
// deep -- the common case, where what dies is a node and a few children,
// costs a direct call and leaves the children's memory warm -- and past that
// is queued on the thread's heap (pool.h), which the outermost free drains.
[[gnu::noinline]] inline void
free_block(const void *block, pool_detail::destroy_fn destroy) noexcept {
  pool_detail::thread_heap &h = pool_detail::this_thread_heap();
  CRANE_STAT(block_free);
  if (h.depth != 0) {
    h.reclaim({block, destroy});
    return;
  }
  h.depth = 1;
  destroy(block, h);
  while (h.size != 0) {
    pool_detail::pending_free f = h.items[--h.size];
    CRANE_STAT(block_drain);
    f.destroy(f.block, h);
  }
  h.depth = 0;
}

} // namespace block_detail

// What a shared block starts with.  [destroy] is a function pointer rather
// than a virtual destructor so the header is two words and what the block
// holds follows it directly; it is handed the heap the block goes back to.
struct shared_block {
  mutable block_detail::count rc;
  const pool_detail::destroy_fn destroy;

  void retain() const noexcept { rc.inc(); }
  // Drops one reference; the last one frees the block, out of line, so the
  // decrement and test are all that is inlined where a reference dies.
  void release() const noexcept {
    if (rc.dec())
      block_detail::free_block(this, destroy);
  }
  // [release] from inside a block's [destroy], which is handed the heap: the
  // last reference frees the block through it ([thread_heap::reclaim]),
  // where [free_block] would first look the heap up -- on Darwin a call per
  // freed child.
  void release_into(pool_detail::thread_heap &h) const noexcept {
    if (rc.dec())
      h.reclaim({this, destroy});
  }
};

// Releases what [x] holds into [h], from inside a [destroy], and leaves it
// empty, so that its destructor, run next, releases nothing: a handle by its
// own [release_into], a generated inductive by its variant's, anything else
// not at all -- its destructor does the work.
template <class T> void release_into(T &x, pool_detail::thread_heap &h) noexcept {
  if constexpr (requires { x.release_into(h); })
    x.release_into(h);
  else if constexpr (requires { x.v_mut().release_into(h); })
    x.v_mut().release_into(h);
}

namespace immortal_detail {

// The walk [crane::make_immortal] does, past a bounded depth: what is left
// to mark, each object with the function that marks it.  A constant can be
// as long as the program's longest list -- a table built at startup -- and
// marked recursively that is one C++ frame per node, so past [max_depth]
// frames an object is queued and the outermost call drains the queue.  An
// object queued is inside a block already immortal, or in the root the
// outermost call was handed, so it is still there when its turn comes.
struct pending {
  const void *object;
  void (*mark)(const void *) noexcept;
};
struct walk {
  std::size_t depth = 0, size = 0, cap = 0;
  pending *items = nullptr;
  void push(pending p) noexcept {
    if (size == cap) {
      std::size_t ncap = cap ? 2 * cap : 64;
      auto *n = static_cast<pending *>(::operator new(ncap * sizeof(pending)));
      for (std::size_t i = 0; i < size; ++i) n[i] = items[i];
      ::operator delete(items);
      items = n;
      cap = ncap;
    }
    items[size++] = p;
  }
};
// Read only while a constant is being marked, once per constant: no path a
// running program repeats reaches this thread_local.
inline walk &this_thread_walk() noexcept {
  thread_local walk w;
  return w;
}
inline constexpr std::size_t max_depth = 256;

template <class T>
concept tuple_like = requires { std::tuple_size<T>::value; };
// A record: a plain aggregate whose fields bind as a pack.  Standard layout
// says its fields are declared in one class, with one access, as a
// structured binding needs.  Binding them as a pack is C++26: an older
// standard (a BDE build) leaves a record's blocks counted.
#if __cplusplus > 202302L
template <class T>
concept plain_record =
    std::is_class_v<T> && std::is_aggregate_v<T> && std::is_standard_layout_v<T> && !std::is_empty_v<T>;
#else
template <class T>
concept plain_record = false;
#endif
template <class T>
concept optional_like = requires(const T &x) {
  typename T::value_type;
  { x.has_value() } -> std::same_as<bool>;
  *x;
};

// Whether [T] may hold a block [make_immortal] can reach.
template <class T>
concept may_hold_blocks =
    !std::is_scalar_v<T>
    && (requires(const T &x) { x.make_immortal(); } || requires(const T &x) { x.v().make_immortal(); }
        || tuple_like<T> || plain_record<T> || optional_like<T>);

template <class T> void mark(const void *p) noexcept;

} // namespace immortal_detail

// Makes every block [x] holds immortal: a handle by its own
// [make_immortal], a generated inductive by its variant's, a pair, tuple,
// optional or record by its components'.  What holds no block of Crane's
// runtime -- a [std::shared_ptr], an immer container -- stays counted.
template <class T> void make_immortal(const T &x) noexcept {
  if constexpr (immortal_detail::may_hold_blocks<T>) {
    immortal_detail::walk &w = immortal_detail::this_thread_walk();
    if (w.depth >= immortal_detail::max_depth) {
      w.push({&x, &immortal_detail::mark<T>});
      return;
    }
    ++w.depth;
    immortal_detail::mark<T>(&x);
    if (w.depth == 1)
      while (w.size != 0) {
        immortal_detail::pending p = w.items[--w.size];
        p.mark(p.object);
      }
    --w.depth;
  }
}

template <class T> void immortal_detail::mark(const void *p) noexcept {
  const T &x = *static_cast<const T *>(p);
  if constexpr (requires { x.make_immortal(); })
    x.make_immortal();
  else if constexpr (requires { x.v().make_immortal(); })
    x.v().make_immortal();
  else if constexpr (optional_like<T>) {
    if (x.has_value()) crane::make_immortal(*x);
  } else if constexpr (tuple_like<T>) {
    [&]<std::size_t... I>(std::index_sequence<I...>) {
      using std::get;
      (crane::make_immortal(get<I>(x)), ...);
    }(std::make_index_sequence<std::tuple_size<T>::value>{});
  }
#if __cplusplus > 202302L
  else {
    const auto &[... fields] = x;
    (crane::make_immortal(fields), ...);
  }
#endif
}

// [v], every block it holds made immortal: a constant -- a function's,
// declared once as a static local, [static const auto pos_10 =
// crane::immortal(...)], or a global's initialiser -- read from every
// thread, which then never write its counts, and never freed.
template <class T> T immortal(T v) {
  crane::make_immortal(v);
  return v;
}

CRANE_RC_POLICY_END

} // namespace crane
