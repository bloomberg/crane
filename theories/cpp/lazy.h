// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#pragma once
#include <cstdint>
#include <cstring>
#include <exception>
#include <new>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include "fn.h"
#include "stats.h"
#include "word.h"

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
// word, shared by every copy, so a copy neither re-runs the computation nor
// copies what it computed -- a coinductive value is copied freely (captured
// by value in the next thunk, returned, converted).
//
// The word is null, or the address of a heap node in one of five states:
//   - a thunk producing the value,
//   - a thunk producing another [lazy] whose value this one is -- what a
//     body that returns an existing coinductive value suspends to,
//   - the value,
//   - a link to the [lazy] such a thunk produced,
//   - the exception such a thunk threw.
// A thunk that throws is not run again: it may have moved out of what it
// captured before it threw.  Its exception is kept, and every later force
// rethrows it, as OCaml's [Lazy.force] may.
// Forcing replaces a thunk by what it produced and so releases the thunk
// and everything it held onto.  A link is followed, never copied through:
// [force] hands out a reference to the one value the chain ends at.
//
// A value that is itself one word naming its own block (a word owner,
// word.h) -- a coinductive's evaluated interaction-tree layer -- needs no
// node: the [lazy] holds it in its word, as OCaml's [Lazy.from_val] holds an
// evaluated value, and tells it from a node by asking the value's type
// whether the block is one of its own.  Both are counted blocks, so a copy
// is the same count bump either way.
template <typename T> class lazy {
  template <typename> friend class lazy;

public:
  // A copy is a refcount bump (see field.h), and the value is one counted
  // word: null, an odd tag, or the address of a [shared_block] (see obj.h).
  using crane_cheap_copy = void;
  using crane_counted_word = void;

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

  // Whether a value is held in the word (see above).  Asked only where [T]
  // is complete.
  static constexpr bool direct() { return word_detail::is_word_owner<T>(); }

  // The word: a node's address as a [base *], or a direct value's bytes.
  alignas(void *) unsigned char w_[sizeof(void *)] = {};

  base *word() const noexcept {
    base *w;
    std::memcpy(&w, w_, sizeof w);
    return w;
  }
  void set_word(base *w) noexcept { std::memcpy(w_, &w, sizeof w); }
  std::uintptr_t bits() const noexcept { return reinterpret_cast<std::uintptr_t>(word()); }
  // The block the word counts, if any: not null, not an odd tag.
  base *counted() const noexcept {
    std::uintptr_t b = bits();
    return b != 0 && (b & 1) == 0 ? word() : nullptr;
  }
  // Whether the word is a value rather than a node.
  bool holds_value() const noexcept {
    if constexpr (direct()) {
      std::uintptr_t b = bits();
      if (b == 0) return false;
      if (b & 1) return true;
      return word_detail::owns_destroy<T>(word()->destroy);
    } else
      return false;
  }
  // The node, when the word is not a value.
  node *nd() const noexcept { return static_cast<node *>(word()); }
  const T &value() const noexcept { return *std::launder(reinterpret_cast<const T *>(w_)); }
  T &value() noexcept { return *std::launder(reinterpret_cast<T *>(w_)); }

  explicit lazy(node *p) noexcept { set_word(static_cast<base *>(p)); }
  // A lazy over the block [b] another lazy's word named, now counted here too.
  static lazy of_word(const base *b) noexcept {
    b->rc.inc();
    lazy r;
    r.set_word(const_cast<base *>(b));
    return r;
  }
  void release() noexcept { lazy_detail::release(counted()); }

  // [v] held in the word, unless its word is null -- a value that names no
  // block and no alternative, which would read as no value at all.
  template <typename... A> void hold(A &&...a) {
    ::new (static_cast<void *>(w_)) T(std::forward<A>(a)...);
    if (word() == nullptr) [[unlikely]] {
      T v(std::move(value()));
      set_word(static_cast<base *>(new node(std::in_place_index<2>, std::move(v))));
      CRANE_STAT(lazy_value);
    } else
      CRANE_STAT(lazy_direct);
  }

public:
  // No node: the state a moved-from value is in, given a name so that a
  // slot written before it is read (a loop's result) can start there.
  lazy() = default;

  explicit lazy(T value) {
    if constexpr (direct())
      hold(std::move(value));
    else {
      set_word(static_cast<base *>(new node(std::in_place_index<2>, std::move(value))));
      CRANE_STAT(lazy_value);
    }
  }

  // The value built in place from [a]: no move of it on the way in.
  template <typename... A> explicit lazy(std::in_place_t, A &&...a) {
    if constexpr (direct())
      hold(std::forward<A>(a)...);
    else {
      set_word(static_cast<base *>(new node(std::in_place_index<2>, std::forward<A>(a)...)));
      CRANE_STAT(lazy_value);
    }
  }

  explicit lazy(fn<T()> thunk) {
    set_word(static_cast<base *>(new node(std::in_place_index<0>, std::move(thunk))));
    CRANE_STAT(lazy_thunk);
  }

  // The value of whatever [thunk] returns, once it is asked for: a [lazy];
  // a coinductive value, which is one wrapped around its [lazy_cell()]; or
  // what a [T] is built from -- a constructor's fields, which then go
  // straight into this node, with no cell of their own on the way.  The
  // thunk is kept in the node ([thunk_node]).
  template <typename F> static lazy delegate(F &&thunk) {
    using R = std::remove_cvref_t<decltype(thunk())>;
    CRANE_STAT(lazy_thunk);
    if constexpr (requires(const R &r) { r.lazy_cell(); }) {
      // [mutable]: a generated thunk is, and may move out of what it holds,
      // since it runs once.
      auto cell = [f = std::forward<F>(thunk)]() mutable -> lazy { return f().lazy_cell(); };
      return lazy(thunk_node<decltype(cell)>::make(std::move(cell)));
    } else
      return lazy(thunk_node<std::decay_t<F>>::make(std::forward<F>(thunk)));
  }

  lazy(const lazy &o) noexcept {
    std::memcpy(w_, o.w_, sizeof w_);
    if (base *b = counted())
      b->rc.inc();
  }
  lazy(lazy &&o) noexcept {
    std::memcpy(w_, o.w_, sizeof w_);
    o.set_word(nullptr);
  }
  // [o] may live inside the node this one releases -- [l = field_of(l)] --
  // so its word is read before anything is released.
  lazy &operator=(const lazy &o) noexcept {
    lazy copy(o);
    std::swap(w_, copy.w_);
    return *this;
  }
  lazy &operator=(lazy &&o) noexcept {
    lazy taken(std::move(o));
    std::swap(w_, taken.w_);
    return *this;
  }
  ~lazy() { release(); }

  // [crane::release_into]: the word's block released into [h], this cell
  // empty.
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (base *b = counted()) b->release_into(h);
    set_word(nullptr);
  }

  // The cell of a value converted from [source] by [thunk].  A coinductive
  // value converts lazily, one layer per conversion; a value that goes out
  // to an erased instantiation and back -- the loop state of an erased
  // [MonadIter], every iteration -- would pile up a layer per round trip,
  // and forcing the k-th step would walk k of them.  Converting back to the
  // type the source was itself converted from is the source.  The thunk is
  // kept in the node ([thunk_node]), and the value it builds goes straight
  // in: one block per conversion.  The source is remembered by its word's
  // block, a node or a direct value's own.
  template <typename S, typename F>
  static lazy converted_from(const lazy<S> &source, F &&thunk) {
    const base *src = source.counted();
    if (src && !source.holds_value() && source.nd()->origin_tag == &tag) {
      CRANE_STAT(lazy_roundtrip);
      return of_word(source.nd()->origin);
    }
    CRANE_STAT(lazy_convert);
    lazy converted(thunk_node<std::decay_t<F>>::make(std::forward<F>(thunk)));
    if (src) {
      src->rc.inc();
      converted.nd()->origin = src;
      converted.nd()->origin_tag = &lazy<S>::tag;
    }
    return converted;
  }

  const T &force() const {
    if constexpr (direct())
      if (holds_value()) {
        CRANE_STAT(lazy_force_direct);
        return value();
      }
    node *start = nd();
    if (!start)
      throw std::logic_error("crane: forced a lazy value that holds nothing");
    // Run what is pending until the chain from here ends at a value.
    CRANE_STAT(lazy_force);
#ifdef CRANE_STATS
    if (start->state.index() == 2)
      CRANE_STAT(lazy_force_value);
#endif
    node *end = start;
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
          end->state.template emplace<6>(std::current_exception());
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
          end->state.template emplace<6>(std::current_exception());
          throw;
        }
        continue;
      }
      case 3:
        CRANE_STAT(lazy_link);
        end = std::get<3>(end->state).nd();
        continue;
      case 4:
        throw std::logic_error(
            "crane: a lazy value was forced while it was being computed");
      case 6:
        std::rethrow_exception(std::get<6>(end->state));
      default:
        break;
      }
      break;
    }
    // Point every link walked straight at that value, so no later force
    // walks the chain again: a loop that delegates at each step would
    // otherwise make its k-th force take k steps.
    lazy held; // the node being retargeted, once nothing else may hold it
    for (node *n = start; n != end;) {
      lazy next = std::get<3>(n->state);
      if (next.nd() != end) {
        end->rc.inc();
        CRANE_STAT(lazy_compress);
        n->state.template emplace<3>(lazy(end));
      }
      n = next.nd();
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
  // [thunk_node]'s thunk, not yet run.  [std::exception_ptr] is what a
  // thunk threw, rethrown by every later force.
  std::variant<fn<T()>, fn<lazy()>, T, lazy, std::monostate, pending,
               std::exception_ptr>
      state;

  // The cell a thunk produced, as this one's: its value moved in where no
  // one else holds it and it has one -- the fresh [go(...)] a corecursive
  // body returns -- so that no chain is left to walk and its block goes
  // back while it is warm; a link to it otherwise.
  void adopt(lazy r) {
    if constexpr (direct())
      if (r.holds_value()) {
        CRANE_STAT(lazy_adopt);
        state.template emplace<2>(std::move(r.value()));
        r.set_word(nullptr);
        return;
      }
    node *q = r.nd();
    if (q && q->rc.sole() && q->state.index() == 2) {
      CRANE_STAT(lazy_adopt);
      state.template emplace<2>(std::move(std::get<2>(q->state)));
    } else
      state.template emplace<3>(std::move(r));
  }

  // Runs the thunk in alternative [From] and stores its result as [To].  A
  // thunk that throws leaves its exception in the node.
  template <std::size_t From, std::size_t To> void run() {
    auto thunk = std::get<From>(std::move(state));
    state.template emplace<4>();
    try {
      state.template emplace<To>(thunk());
    } catch (...) {
      state.template emplace<6>(std::current_exception());
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
  // The thunk's result; a thunk that throws is let go of here, and [force]
  // keeps its exception in the state.
  decltype(auto) call() {
    try {
      return f();
    } catch (...) {
      f.~F();
      throw;
    }
  }
  static void run_it(node *n) {
    auto *self = static_cast<thunk_node *>(n);
    if constexpr (std::is_same_v<std::remove_cvref_t<decltype(self->f())>, lazy>) {
      lazy r = self->call();
      self->f.~F();
      n->adopt(std::move(r));
    } else {
      n->state.template emplace<2>(self->call());
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
