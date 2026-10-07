// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::shared_variant: the tagged union of an inductive whose values are
// shared rather than copied, under `Set Crane SharedVariant`.
//
// A value is one word.  An alternative with fields lives in a counted block
// of its own -- a [shared_block] followed by the alternative -- and the word
// is the block's address; an alternative with no fields ([Leaf], [Nil], [O])
// is an odd word carrying its index, and allocates nothing.  So copying a
// value is a count increment, moving it is a word move, and a node built from
// existing children shares their blocks instead of copying them -- the
// representation OCaml gives an inductive, and the one Perceus recycles.
//
// It offers crane::variant's interface: holds_alternative, get, get_if,
// index, emplace.  Reading is through a const view and never copies.  Writing
// through a non-const view first makes the block unique, copying it if it is
// shared, so a value held twice is never changed under its other holder.
//
// Blocks come from the thread's pool and are freed by [free_block], which
// queues a free that happens during another instead of recursing: dropping
// the last reference to a long list or a deep tree takes constant stack.
//
// crane::box<T> is the slot a recursive field holds a shared value in.  T is
// incomplete where the slot is declared -- inside its own alternatives -- so
// the slot reserves a shared value's one word and checks the fit where T is
// complete.  The word 0, which no shared value uses, is the empty slot.

#ifndef INCLUDED_CRANE_SHARED_VARIANT
#define INCLUDED_CRANE_SHARED_VARIANT

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <new>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>

#include "shared_block.h"

namespace crane {

CRANE_RC_POLICY_BEGIN

template <class... Ts> class shared_variant {
  static_assert(sizeof...(Ts) > 0, "crane::shared_variant: at least one alternative");

  template <std::size_t I> using alt = std::tuple_element_t<I, std::tuple<Ts...>>;

  template <class T> static constexpr std::size_t index_of() {
    std::size_t k = 0, r = sizeof...(Ts);
    ((std::is_same_v<T, Ts> && r == sizeof...(Ts) ? r = k : 0, ++k), ...);
    return r;
  }

  // The block an alternative with fields lives in.  Its [destroy] is the
  // alternative's own, which is how the block says which alternative it
  // holds.
  template <std::size_t I>
  struct block : shared_block, pool_detail::pooled<block<I>> {
    alt<I> value;
    template <class... A>
    explicit block(A &&...a) : shared_block{{}, &drop}, value(std::forward<A>(a)...) {}
    static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
      block::dispose(static_cast<const block *>(static_cast<const shared_block *>(b)), h);
    }
  };

  template <std::size_t I> static constexpr bool inline_alt = std::is_empty_v<alt<I>>;

  // 0: moved from, no alternative.  Odd: an alternative with no fields, its
  // index above the tag bit.  Otherwise the address of a block.
  std::uintptr_t w_;

  static constexpr std::uintptr_t tag(std::size_t i) { return (std::uintptr_t(i) << 1) | 1; }
  bool boxed() const { return w_ != 0 && (w_ & 1) == 0; }
  const shared_block *hdr() const { return reinterpret_cast<const shared_block *>(w_); }
  template <std::size_t I> block<I> *blk() const {
    return static_cast<block<I> *>(const_cast<shared_block *>(hdr()));
  }

  template <std::size_t I> bool is() const {
    if constexpr (inline_alt<I>) return w_ == tag(I);
    else return boxed() && hdr()->destroy == &block<I>::drop;
  }

  template <std::size_t I, class... A> static std::uintptr_t make(A &&...a) {
    if constexpr (inline_alt<I>) return tag(I);
    else return reinterpret_cast<std::uintptr_t>(
        static_cast<shared_block *>(new block<I>(std::forward<A>(a)...)));
  }

  void release() {
    if (boxed()) hdr()->release();
  }

  // f(integral_constant<I>) for the active index I.
  template <class F> void on_index(F &&f) const {
    [&]<std::size_t... I>(std::index_sequence<I...>) {
      (void)((is<I>() ? (f(std::integral_constant<std::size_t, I>{}), true) : false) || ...);
    }(std::index_sequence_for<Ts...>{});
  }

  // A block no other value holds, copying this one's if it is shared.
  void make_unique() {
    if (boxed() && !hdr()->rc.sole()) {
      on_index([&](auto i) {
        constexpr std::size_t I = decltype(i)::value;
        if constexpr (!inline_alt<I>) {
          std::uintptr_t fresh = make<I>(std::as_const(blk<I>()->value));
          release();
          w_ = fresh;
        }
      });
    }
  }

  template <std::size_t I> alt<I> &raw() const {
    if constexpr (inline_alt<I>) {
      static alt<I> empty{};
      return empty;
    } else {
      return blk<I>()->value;
    }
  }

public:
  shared_variant() : w_(make<0>()) {}
  shared_variant(const shared_variant &o) : w_(o.w_) {
    if (boxed()) hdr()->retain();
  }
  shared_variant(shared_variant &&o) noexcept : w_(std::exchange(o.w_, 0)) {}

  template <class T, class D = std::decay_t<T>,
            class = std::enable_if_t<(index_of<D>() < sizeof...(Ts))>>
  shared_variant(T &&t) : w_(make<index_of<D>()>(std::forward<T>(t))) {}

  template <std::size_t I, class... A>
  explicit shared_variant(std::in_place_index_t<I>, A &&...a) : w_(make<I>(std::forward<A>(a)...)) {}

  // [o] may live inside the block this one releases, so it is taken first.
  shared_variant &operator=(const shared_variant &o) {
    shared_variant copy(o);
    std::swap(w_, copy.w_);
    return *this;
  }
  shared_variant &operator=(shared_variant &&o) noexcept {
    shared_variant taken(std::move(o));
    std::swap(w_, taken.w_);
    return *this;
  }
  template <class T, class D = std::decay_t<T>,
            class = std::enable_if_t<(index_of<D>() < sizeof...(Ts))>>
  shared_variant &operator=(T &&t) {
    emplace<index_of<D>()>(std::forward<T>(t));
    return *this;
  }

  template <std::size_t I, class... A> alt<I> &emplace(A &&...a) {
    std::uintptr_t fresh = make<I>(std::forward<A>(a)...);
    release();
    w_ = fresh;
    return raw<I>();
  }

  ~shared_variant() { release(); }

  std::size_t index() const {
    std::size_t r = std::variant_npos;
    on_index([&](auto i) { r = decltype(i)::value; });
    return r;
  }

  template <class T> bool holds() const { return is<index_of<T>()>(); }

  // Whether no other value shares this one's block.
  bool unique() const { return !boxed() || hdr()->rc.sole(); }

  // How many values share this one's block: 1 for an alternative with no
  // fields, which no one shares because there is nothing to share.
  std::size_t use_count() const {
    if (!boxed()) return 1;
    if constexpr (requires { hdr()->rc.n.load(); }) return hdr()->rc.n.load(std::memory_order_acquire);
    else return hdr()->rc.n;
  }

  template <std::size_t I> const alt<I> &at() const {
    if (!is<I>()) [[unlikely]]
      throw std::bad_variant_access();
    return raw<I>();
  }
  template <std::size_t I> alt<I> &at() {
    if (!is<I>()) [[unlikely]]
      throw std::bad_variant_access();
    make_unique();
    return raw<I>();
  }
  template <std::size_t I> const alt<I> *at_if() const { return is<I>() ? &raw<I>() : nullptr; }
  template <std::size_t I> alt<I> *at_if() {
    if (!is<I>()) return nullptr;
    make_unique();
    return &raw<I>();
  }

  template <class T> static constexpr std::size_t index_of_alt = index_of<T>();
};

template <class T, class... Ts> bool holds_alternative(const shared_variant<Ts...> &v) {
  return v.template holds<T>();
}
template <std::size_t I, class... Ts> decltype(auto) get(shared_variant<Ts...> &v) {
  return v.template at<I>();
}
template <std::size_t I, class... Ts> decltype(auto) get(const shared_variant<Ts...> &v) {
  return v.template at<I>();
}
template <class T, class... Ts> T &get(shared_variant<Ts...> &v) {
  return v.template at<shared_variant<Ts...>::template index_of_alt<T>>();
}
template <class T, class... Ts> const T &get(const shared_variant<Ts...> &v) {
  return v.template at<shared_variant<Ts...>::template index_of_alt<T>>();
}
template <class T, class... Ts> T *get_if(shared_variant<Ts...> *v) {
  return v ? v->template at_if<shared_variant<Ts...>::template index_of_alt<T>>() : nullptr;
}
template <class T, class... Ts> const T *get_if(const shared_variant<Ts...> *v) {
  return v ? v->template at_if<shared_variant<Ts...>::template index_of_alt<T>>() : nullptr;
}

// The slot a recursive field holds a shared value in: the value itself, in
// place, in one word, with 0 for empty.
template <class T> class box {
  alignas(void *) unsigned char s_[sizeof(void *)] = {};

  static constexpr void fits() {
    static_assert(sizeof(T) == sizeof(void *) && alignof(T) <= alignof(void *),
                  "crane::box<T>: T must be one shared_variant");
  }
  bool full() const {
    std::uintptr_t w;
    std::memcpy(&w, s_, sizeof w);
    return w != 0;
  }
  T *ptr() const { return std::launder(reinterpret_cast<T *>(const_cast<unsigned char *>(s_))); }

public:
  using element_type = T;
  // A copy is a count bump.
  using crane_cheap_copy = void;

  box() = default;
  box(std::nullptr_t) noexcept {}
  // The value built in place from [a], as [make_rc<T>(a...)] would build it.
  template <class... A> static box make(A &&...a) {
    fits();
    box b;
    ::new (b.s_) T(std::forward<A>(a)...);
    return b;
  }
  box(const box &o) {
    if (o.full()) ::new (s_) T(*o.ptr());
  }
  box(box &&o) noexcept {
    std::memcpy(s_, o.s_, sizeof s_);
    std::memset(o.s_, 0, sizeof o.s_);
  }
  box &operator=(box o) noexcept {
    std::swap(s_, o.s_);
    return *this;
  }
  box &operator=(std::nullptr_t) noexcept {
    box empty;
    std::swap(s_, empty.s_);
    return *this;
  }
  ~box() {
    if (full()) ptr()->~T();
  }

  // How many values share the held value's block, as [crane::rc] counts
  // owners; 0 for an empty slot.
  std::size_t use_count() const { return full() ? ptr()->v().use_count() : 0; }

  T &operator*() const { return *ptr(); }
  T *operator->() const { return ptr(); }
  T *get() const { return full() ? ptr() : nullptr; }
  explicit operator bool() const { return full(); }
  friend bool operator==(const box &b, std::nullptr_t) { return !b.full(); }

  void reset() noexcept { *this = nullptr; }
};

CRANE_RC_POLICY_END

} // namespace crane

// [crane_raw] for a shared slot: the value it holds, or null.
template <typename T> T *crane_raw(const crane::box<T> &p) noexcept { return p.get(); }

#endif // INCLUDED_CRANE_SHARED_VARIANT
