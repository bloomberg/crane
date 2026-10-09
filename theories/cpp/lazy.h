// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#pragma once
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include "fn.h"

namespace crane {

CRANE_RC_POLICY_BEGIN

namespace lazy_detail {
// What a node of any instantiation starts with, so that a converted cell can
// own the cell it was converted from without knowing its type.
using base = shared_block;
inline void release(const base *b) noexcept {
  if (b)
    b->release();
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

public:
  // A copy is a refcount bump (see field.h).
  using crane_cheap_copy = void;

private:
  using base = lazy_detail::base;

  // Defined below: its state holds a [lazy], complete only there.
  struct node;
  // A node holding its thunk in place, rather than in an [fn] of its own:
  // one block where there would be two.
  template <typename F> struct thunk_node;
  // The state of a [thunk_node] whose thunk has not run: how to run it and
  // store what it produced.
  struct pending {
    void (*run)(node *);
  };

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

  // The value built in the node from [a]: no move of it on the way in.
  template <typename... A>
  explicit lazy(std::in_place_t, A &&...a)
      : p_(new node(std::in_place_index<2>, std::forward<A>(a)...)) {}

  explicit lazy(fn<T()> thunk)
      : p_(new node(std::in_place_index<0>, std::move(thunk))) {}

  // The value of whatever [thunk] returns, once it is asked for: a [lazy];
  // a coinductive value, which is one wrapped around its [lazy_cell()]; or
  // what a [T] is built from -- a constructor's fields, which then go
  // straight into this node, with no cell of their own on the way.  The
  // thunk is kept in the node ([thunk_node]).
  template <typename F> static lazy delegate(F &&thunk) {
    using R = std::remove_cvref_t<decltype(thunk())>;
    if constexpr (requires(const R &r) { r.lazy_cell(); }) {
      auto cell = [f = std::forward<F>(thunk)]() -> lazy { return f().lazy_cell(); };
      return lazy(thunk_node<decltype(cell)>::make(std::move(cell)));
    } else
      return lazy(thunk_node<std::decay_t<F>>::make(std::forward<F>(thunk)));
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

  // [crane::release_into]: the node released into [h], this cell empty.
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (p_) p_->release_into(h);
    p_ = nullptr;
  }

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
    if (!p_)
      throw std::logic_error("crane: forced a lazy value that holds nothing");
    // Run what is pending until the chain from here ends at a value.
    node *end = p_;
    for (;;) {
      switch (end->state.index()) {
      case 0:
        end->template run<0, 2>();
        break;
      case 1: {
        auto thunk = std::get<1>(std::move(end->state));
        end->state.template emplace<4>();
        lazy r;
        try {
          r = thunk();
        } catch (...) {
          end->state.template emplace<1>(std::move(thunk));
          throw;
        }
        thunk = nullptr;
        end->adopt(std::move(r));
        continue;
      }
      case 5: {
        pending p = std::get<5>(end->state);
        end->state.template emplace<4>();
        try {
          p.run(end);
        } catch (...) {
          end->state.template emplace<5>(p);
          throw;
        }
        continue;
      }
      case 3:
        end = std::get<3>(end->state).p_;
        continue;
      case 4:
        throw std::logic_error(
            "crane: a lazy value was forced while it was being computed");
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
  // [std::monostate] marks a thunk that is running: forcing the node again
  // from inside it -- a computation that needs its own result -- is an
  // error, as it is for OCaml's [Lazy.force], and not a second run that
  // would destroy the first one's result under it.  [pending] is a
  // [thunk_node]'s thunk, not yet run.
  std::variant<fn<T()>, fn<lazy()>, T, lazy, std::monostate, pending> state;

  // The cell a thunk produced, as this one's: its value moved in where no
  // one else holds it and it has one -- the fresh [go(...)] a corecursive
  // body returns -- so that no chain is left to walk and its block goes
  // back while it is warm; a link to it otherwise.
  void adopt(lazy r) {
    if (r.p_ && r.p_->rc.sole() && r.p_->state.index() == 2)
      state.template emplace<2>(std::move(std::get<2>(r.p_->state)));
    else
      state.template emplace<3>(std::move(r));
  }

  // Runs the thunk in alternative [From] and stores its result as [To].  A
  // thunk that throws leaves the node as it found it.
  template <std::size_t From, std::size_t To> void run() {
    auto thunk = std::get<From>(std::move(state));
    state.template emplace<4>();
    try {
      state.template emplace<To>(thunk());
    } catch (...) {
      state.template emplace<From>(std::move(thunk));
      throw;
    }
  }
  // The cell this one was converted from, if it was, and the
  // instantiation it has; see [converted_from].
  const base *origin = nullptr;
  const void *origin_tag = nullptr;

  template <typename... A>
  explicit node(A &&...a)
      : base{{}, &drop}, state(std::forward<A>(a)...) {}
  // For a derived node, which frees itself.
  struct with_destroy_t {};
  template <typename... A>
  explicit node(with_destroy_t, pool_detail::destroy_fn d, A &&...a)
      : base{{}, d}, state(std::forward<A>(a)...) {}
  ~node() { lazy_detail::release(origin); }
  static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
    auto *self = static_cast<node *>(const_cast<base *>(static_cast<const base *>(b)));
    if (!self->state.valueless_by_exception())
      std::visit([&](auto &s) { crane::release_into(s, h); }, self->state);
    if (self->origin) self->origin->release_into(h);
    self->origin = nullptr;
    node::dispose(self, h);
  }
};

template <typename T>
template <typename F>
struct lazy<T>::thunk_node : lazy<T>::node {
  // Alive while the state is [pending]: run, the thunk is let go of -- and
  // what it captured -- before a [lazy] it produced is stored, and as soon
  // as a value it produced is built in place.
  union {
    F f;
  };
  template <typename G>
  explicit thunk_node(G &&g)
      : node(typename node::with_destroy_t{}, &drop, std::in_place_index<5>, pending{&run_it}),
        f(std::forward<G>(g)) {}
  ~thunk_node() {
    if (this->state.index() == 5) f.~F();
  }
  template <typename G> static node *make(G &&g) {
    void *p = pool_detail::this_thread_heap().template take<sizeof(thunk_node)>();
    return ::new (p) thunk_node(std::forward<G>(g));
  }
  static void run_it(node *n) {
    auto *self = static_cast<thunk_node *>(n);
    if constexpr (std::is_same_v<std::remove_cvref_t<decltype(self->f())>, lazy>) {
      lazy r = self->f();
      self->f.~F();
      n->adopt(std::move(r));
    } else {
      n->state.template emplace<2>(self->f());
      self->f.~F();
    }
  }
  static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
    auto *self = static_cast<thunk_node *>(
        static_cast<node *>(const_cast<base *>(static_cast<const base *>(b))));
    if (!self->state.valueless_by_exception())
      std::visit([&](auto &s) { crane::release_into(s, h); }, self->state);
    if (self->origin) self->origin->release_into(h);
    self->origin = nullptr;
    self->~thunk_node();
    h.template give<sizeof(thunk_node)>(self);
  }
};

CRANE_RC_POLICY_END

} // namespace crane
