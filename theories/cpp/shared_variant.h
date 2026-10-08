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
// crane::shared_box<T> is the slot a recursive field holds a shared value in.  T is
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
      auto *self = static_cast<block *>(const_cast<shared_block *>(static_cast<const shared_block *>(b)));
      crane::each_field(self->value, [&](auto &x) { crane::release_into(x, h); });
      block::dispose(self, h);
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

  // [crane::release_into]: the block released into [h], this value empty.
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (boxed()) hdr()->release_into(h);
    w_ = 0;
  }

  // Keeps this value's block, and every block it holds, for the rest of the
  // program; see [crane::constant].
  void make_immortal() const {
    if (!boxed() || hdr()->rc.is_immortal()) return;
    hdr()->rc.make_immortal();
    on_index([&](auto i) {
      constexpr std::size_t I = decltype(i)::value;
      if constexpr (!inline_alt<I>)
        crane::each_field(blk<I>()->value, [](const auto &x) { crane::make_immortal(x); });
    });
  }

  // Perceus reuse: when this value is the only one holding its block and the
  // block holds [Alt], [a] replaces what it holds there -- no allocation, and
  // the old fields are released as the assignment overwrites them -- and the
  // answer is true.  Otherwise [a] is left as it was, for the caller to build
  // a fresh value from.
  template <class Alt> bool try_reuse(Alt &&a) {
    constexpr std::size_t I = index_of<std::decay_t<Alt>>();
    if constexpr (inline_alt<I>) {
      return false;
    } else {
      if (!is<I>() || !hdr()->rc.sole()) return false;
      blk<I>()->value = std::move(a);
      return true;
    }
  }

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
template <class T> class shared_box {
  alignas(void *) unsigned char s_[sizeof(void *)] = {};

  static constexpr void fits() {
    static_assert(sizeof(T) == sizeof(void *) && alignof(T) <= alignof(void *),
                  "crane::shared_box<T>: T must be one shared_variant");
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

  shared_box() = default;
  shared_box(std::nullptr_t) noexcept {}
  // The value built in place from [a], as [make_rc<T>(a...)] would build it.
  template <class... A> static shared_box make(A &&...a) {
    fits();
    shared_box b;
    ::new (b.s_) T(std::forward<A>(a)...);
    return b;
  }
  shared_box(const shared_box &o) {
    if (o.full()) ::new (s_) T(*o.ptr());
  }
  shared_box(shared_box &&o) noexcept {
    std::memcpy(s_, o.s_, sizeof s_);
    std::memset(o.s_, 0, sizeof o.s_);
  }
  shared_box &operator=(shared_box o) noexcept {
    std::swap(s_, o.s_);
    return *this;
  }
  shared_box &operator=(std::nullptr_t) noexcept {
    shared_box empty;
    std::swap(s_, empty.s_);
    return *this;
  }
  ~shared_box() {
    if (full()) ptr()->~T();
  }

  // How many values share the held value's block, as [crane::rc] counts
  // owners; 0 for an empty slot.
  std::size_t use_count() const { return full() ? ptr()->v().use_count() : 0; }

  T &operator*() const { return *ptr(); }
  T *operator->() const { return ptr(); }
  T *get() const { return full() ? ptr() : nullptr; }
  explicit operator bool() const { return full(); }
  friend bool operator==(const shared_box &b, std::nullptr_t) { return !b.full(); }

  void reset() noexcept { *this = nullptr; }

  // [crane::release_into]: the held value's block released into [h].
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (full()) crane::release_into(*ptr(), h);
  }
  // [crane::make_immortal]: the held value's blocks.
  void make_immortal() const noexcept {
    if (full()) crane::make_immortal(*ptr());
  }
};

// A closed constructor term, built the first time it is evaluated and kept:
// [f] builds it, and every later evaluation copies it, a count bump.  Its
// blocks are immortal, so the threads that read it never write their counts.
// One [F], one lambda at one site, is one constant.
template <class F> const auto &constant(F f) {
  static const auto k = [&] {
    auto v = f();
    crane::make_immortal(v);
    return v;
  }();
  return k;
}

// Whether a type is an inductive stored as a shared variant.
template <class V> struct is_shared_variant : std::false_type {};
template <class... Ts> struct is_shared_variant<shared_variant<Ts...>> : std::true_type {};
template <class T> constexpr bool stored_shared() {
  if constexpr (requires { typename T::variant_t; })
    return is_shared_variant<typename T::variant_t>::value;
  else
    return false;
}

// The slot for a T a template's body reaches through its parameter -- a
// functor's argument -- which is a shared variant or not according to the
// instantiation: a shared_box if it is, [Pointer] if not.
template <class T, class Pointer>
using shared_or_t = std::conditional_t<stored_shared<T>(), shared_box<T>, Pointer>;

CRANE_RC_POLICY_END

} // namespace crane

// [crane_raw] for a shared slot: the value it holds, or null.
template <typename T> T *crane_raw(const crane::shared_box<T> &p) noexcept { return p.get(); }

#endif // INCLUDED_CRANE_SHARED_VARIANT
