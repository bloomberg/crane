// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#pragma once
#include <type_traits>
#include <utility>
#include <variant>
#include "fn.h"

namespace crane {

namespace lazy_detail {
// What a node of any instantiation starts with, so that a converted cell can
// own the cell it was converted from without knowing its type.
struct base {
  mutable fn_detail::count rc;
  void (*const destroy)(const void *) noexcept;
};
inline void release(const base *b) noexcept {
  if (b && b->rc.dec())
    fn_detail::free_block(b, b->destroy);
}
} // namespace lazy_detail

// A suspended value, evaluated at most once: call-by-need.  A [lazy] is one
// pointer to one heap node, shared by every copy, so a copy neither re-runs
// the computation nor copies what it computed -- a coinductive value is
// copied freely (captured by value in the next thunk, returned, converted).
//
// The node is in one of four states:
//   - a thunk producing the value,
//   - a thunk producing another [lazy] whose value this one is -- what a
//     body that returns an existing coinductive value suspends to,
//   - the value,
//   - a link to the [lazy] such a thunk produced.
// Forcing replaces a thunk by what it produced and so releases the thunk
// and everything it held onto.  A link is followed, never copied through:
// [force] hands out a reference to the one value the chain ends at.
template <typename T> class lazy {
  template <typename> friend class lazy;

  using base = lazy_detail::base;

  // Defined below: its state holds a [lazy], complete only there.
  struct node;

  // One address per instantiation, naming it without RTTI.
  static constexpr char tag = 0;

  node *p_ = nullptr;

  explicit lazy(node *p) noexcept : p_(p) {}
  void release() noexcept { lazy_detail::release(p_); }

public:
  // No node: the state a moved-from value is in, given a name so that a
  // slot written before it is read (a loop's result) can start there.
  lazy() = default;

  explicit lazy(T value)
      : p_(new node(std::in_place_index<2>, std::move(value))) {}

  explicit lazy(fn<T()> thunk)
      : p_(new node(std::in_place_index<0>, std::move(thunk))) {}

  // The value of whatever [thunk] returns, once it is asked for: a [lazy],
  // or a coinductive value, which is one wrapped around its [lazy_cell()].
  template <typename F> static lazy delegate(F &&thunk) {
    using R = std::remove_cvref_t<decltype(thunk())>;
    if constexpr (std::is_same_v<R, lazy>)
      return lazy(new node(std::in_place_index<1>,
                           fn<lazy()>(std::forward<F>(thunk))));
    else
      return lazy(new node(
          std::in_place_index<1>,
          fn<lazy()>([f = std::forward<F>(thunk)]() -> lazy {
            return f().lazy_cell();
          })));
  }

  lazy(const lazy &o) noexcept : p_(o.p_) {
    if (p_)
      p_->rc.inc();
  }
  lazy(lazy &&o) noexcept : p_(std::exchange(o.p_, nullptr)) {}
  // [o] may live inside the node this one releases -- [l = field_of(l)] --
  // so its pointer is read before anything is released.
  lazy &operator=(const lazy &o) noexcept {
    node *q = o.p_;
    if (q)
      q->rc.inc();
    release();
    p_ = q;
    return *this;
  }
  lazy &operator=(lazy &&o) noexcept {
    node *q = std::exchange(o.p_, nullptr);
    release();
    p_ = q;
    return *this;
  }
  ~lazy() { release(); }

  // The cell of a value converted from [source] by [thunk].  A coinductive
  // value converts lazily, one layer per conversion; a value that goes out
  // to an erased instantiation and back -- the loop state of an erased
  // [MonadIter], every iteration -- would pile up a layer per round trip,
  // and forcing the k-th step would walk k of them.  Converting back to the
  // type the source was itself converted from is the source.
  template <typename S>
  static lazy converted_from(const lazy<S> &source, fn<T()> thunk) {
    const auto *src = source.p_;
    if (src && src->origin_tag == &tag) {
      src->origin->rc.inc();
      return lazy(static_cast<node *>(const_cast<base *>(src->origin)));
    }
    lazy converted(std::move(thunk));
    if (src) {
      src->rc.inc();
      converted.p_->origin = src;
      converted.p_->origin_tag = &lazy<S>::tag;
    }
    return converted;
  }

  const T &force() const {
    // Run what is pending until the chain from here ends at a value.
    node *end = p_;
    for (;;) {
      switch (end->state.index()) {
      case 0: {
        fn<T()> thunk = std::get<0>(end->state);
        end->state.template emplace<2>(thunk());
        break;
      }
      case 1: {
        fn<lazy()> thunk = std::get<1>(end->state);
        end->state.template emplace<3>(thunk());
        continue;
      }
      case 3:
        end = std::get<3>(end->state).p_;
        continue;
      default:
        break;
      }
      break;
    }
    // Point every link walked straight at that value, so no later force
    // walks the chain again: a loop that delegates at each step would
    // otherwise make its k-th force take k steps.
    lazy held; // the node being retargeted, once nothing else may hold it
    for (node *n = p_; n != end;) {
      lazy next = std::get<3>(n->state);
      if (next.p_ != end) {
        end->rc.inc();
        n->state.template emplace<3>(lazy(end));
      }
      n = next.p_;
      held = std::move(next);
    }
    return std::get<2>(end->state);
  }
};

template <typename T>
struct lazy<T>::node : base, pool_detail::pooled<typename lazy<T>::node> {
  std::variant<fn<T()>, fn<lazy()>, T, lazy> state;
  // The cell this one was converted from, if it was, and the
  // instantiation it has; see [converted_from].
  const base *origin = nullptr;
  const void *origin_tag = nullptr;

  template <typename... A>
  explicit node(A &&...a)
      : base{{}, &drop}, state(std::forward<A>(a)...) {}
  ~node() { lazy_detail::release(origin); }
  static void drop(const void *b) noexcept {
    delete static_cast<const node *>(static_cast<const base *>(b));
  }
};

} // namespace crane
