// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::obj -- an erased value, shared rather than copied.
//
// Crane erases a type it cannot name to one uniform representation.  That
// was [std::any], which owns its value: copying an [std::any] copies what it
// holds, so a boxed state pair, a boxed event or a boxed tree was deep-copied
// every time the box was passed on.  A Rocq value is immutable, and an OCaml
// erased value is one word that copying shares; [crane::obj] is the same.  A
// small trivially copyable value (a machine integer, an enum, a bool) is held
// in the handle itself, and so is a value that is itself one counted word --
// a shared variant, a closure, a lazy cell -- whose copy is the count bump a
// box would have cost; anything else lives in one intrusive-counted heap box,
// and copying the handle bumps the count.
//
// Reading a value back is [crane::any_cast], with [std::any_cast]'s
// signature and one difference that follows from sharing: from an lvalue
// handle it hands out a [const T &] into the box instead of a copy, and from
// an rvalue handle it returns a [T] -- moved out when the handle was the
// box's only owner, copied otherwise -- so no reference outlives its box.
// Reading at the wrong type throws [std::bad_any_cast].
#pragma once
#include <any>
#include <cstdint>
#include <cstring>
#include <new>
#include <type_traits>
#include <typeinfo>
#include <utility>
#include "shared_block.h"

namespace crane {

CRANE_RC_POLICY_BEGIN

namespace obj_detail {

template <class T>
inline constexpr bool fits_word = sizeof(T) <= sizeof(void *) && alignof(T) <= alignof(void *);

template <class T>
inline constexpr bool held_inline = std::is_trivially_copyable_v<T> && fits_word<T>;

// A value that is one counted word: null, an odd tag (a shared variant's
// alternative with no fields), or the address of a [shared_block] at the
// start of a counted block -- a shared variant, a closure, a lazy cell, or a
// generated type wrapping one ([crane_counted_word]).  It is held in the
// handle itself, as the word: copying it is the count bump a box would have
// cost, done here, and dropping it a release.
template <class T>
inline constexpr bool held_handle =
    !held_inline<T> && fits_word<T> &&
    (requires { typename T::crane_counted_word; } ||
     requires { typename T::variant_t::crane_counted_word; } ||
     requires(const T &t) { t.lazy_cell(); });

template <class T> inline constexpr bool held_in_place = held_inline<T> || held_handle<T>;

template <class T> struct box : shared_block, pool_detail::pooled<box<T>> {
  T value;
  template <class... A>
  explicit box(A &&...a)
      : shared_block{{}, &drop}, value(std::forward<A>(a)...) {}
  static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
    auto *self = static_cast<box *>(const_cast<shared_block *>(static_cast<const shared_block *>(b)));
    crane::release_into(self->value, h);
    box::dispose(self, h);
  }
};

// One per held type: what the handle's tag points at.  [inline_] is a value
// held in the handle and [counted] one that is a counted word; [immortalize]
// makes the box, or the word, and every block it holds immortal.
//
// [held] is the tag of the held type itself: a value boxed as itself and
// readable at another type too ([erased]) has a tag of its own, and is still
// read at its own type through [held].  [erased], when set, is the tag of the
// instantiation code that erased the type's parameters reads the value at
// (see [obj::viewed_as]), and [to_erased] builds the value at it.
struct type_tag {
  const std::type_info &info;
  bool inline_;
  bool counted;
  void (*immortalize)(const void *) noexcept;
  const type_tag *held;
  const type_tag *erased;
  void (*to_erased)(const void *, void *);
};
template <class T> void immortalize(const void *p) noexcept {
  if constexpr (held_handle<T>) {
    crane::make_immortal(*static_cast<const T *>(p));
  } else {
    auto *b = static_cast<const shared_block *>(p);
    if (b->rc.is_immortal()) return;
    b->rc.make_immortal();
    crane::make_immortal(static_cast<const box<T> *>(b)->value);
  }
}
template <class T>
inline constexpr type_tag tag_of{typeid(T), held_in_place<T>, held_handle<T>, &immortalize<T>, &tag_of<T>,
                                 nullptr, nullptr};

// The tag of a counted word [S] boxed as itself and read, where code that
// erased its type's parameters reads it, at [E] -- built by [Conv].
template <class S, class E, void (*Conv)(const void *, void *)>
inline constexpr type_tag tag_viewed{typeid(S), true, true, &immortalize<S>, &tag_of<S>, &tag_of<E>, Conv};

// Whether [T] is a generated inductive at the instantiation code that
// erased its parameters builds and reads it at: every argument [crane::obj].
template <class T, class O> struct all_obj : std::false_type {};
template <template <class...> class C, class... A, class O>
  requires requires { typename C<A...>::variant_t; }
struct all_obj<C<A...>, O> : std::bool_constant<(sizeof...(A) > 0) && (std::is_same_v<A, O> && ...)> {};

} // namespace obj_detail

class obj {
public:
  // A copy is a refcount bump, or a word's copy (see field.h).
  using crane_cheap_copy = void;

private:
  const obj_detail::type_tag *tag_ = nullptr;
  // [bytes_] is not a character array, which in a local -- and
  // a generated function holds many such values -- makes the compiler guard
  // the function's stack (-fstack-protector), a canary load and check on
  // every call.  It is only ever read and written whole, through
  // [std::memcpy], or as the object built in it.
  union {
    const shared_block *box_;
    std::uintptr_t bytes_[1];
  };

  bool boxed() const noexcept { return tag_ && !tag_->inline_; }
  // The block this holds a count on: a box, or what a counted word names.
  const shared_block *counted_block() const noexcept {
    if (!tag_) return nullptr;
    if (!tag_->inline_) return box_;
    if (!tag_->counted) return nullptr;
    const shared_block *p;
    std::memcpy(&p, bytes_, sizeof p);
    const std::uintptr_t w = reinterpret_cast<std::uintptr_t>(p);
    return w != 0 && (w & 1) == 0 ? p : nullptr;
  }
  void release() noexcept {
    if (auto *b = counted_block())
      b->release();
  }

  template <class T> friend const T *any_cast(const obj *) noexcept;
  template <class T> friend T *any_cast(obj *) noexcept;
  template <class T> friend std::remove_cvref_t<T> any_cast(obj &&);

public:
  obj() noexcept : box_(nullptr) {}

  template <class V, class T = std::decay_t<V>>
    requires(!std::is_same_v<T, obj> && std::is_copy_constructible_v<T>)
  obj(V &&v) : tag_(&obj_detail::tag_of<T>) {
    if constexpr (obj_detail::held_in_place<T>)
      ::new (static_cast<void *>(bytes_)) T(std::forward<V>(v));
    else
      box_ = new obj_detail::box<T>(std::forward<V>(v));
  }

  // [v], a counted word, boxed as itself, and readable at [E] too: the
  // instantiation code that erased its type's parameters reads it at.  [Conv]
  // builds it at [E] -- one level, its fields boxed in turn -- only for a
  // reader at [E].  Boxing it at [E] up front would rebuild it, and every
  // value under it, for a reader that, more often than not, reads it back at
  // the type it had.
  template <class E, void (*Conv)(const void *, void *)> struct viewed_as {};
  template <class V, class E, void (*Conv)(const void *, void *), class S = std::decay_t<V>>
    requires obj_detail::held_handle<S>
  obj(viewed_as<E, Conv>, V &&v) : tag_(&obj_detail::tag_viewed<S, E, Conv>) {
    ::new (static_cast<void *>(bytes_)) S(std::forward<V>(v));
  }

  // The held value at [U], the type it is readable at besides its own (see
  // [viewed_as]); [std::bad_any_cast] if it is not.
  template <class U> U read_erased() const {
    if (!tag_ || tag_->erased != &obj_detail::tag_of<U>)
      throw std::bad_any_cast();
    alignas(U) unsigned char buf[sizeof(U)];
    tag_->to_erased(bytes_, buf);
    U *p = std::launder(reinterpret_cast<U *>(buf));
    U r(std::move(*p));
    p->~U();
    return r;
  }
  template <class U> bool reads_erased_as() const noexcept {
    return tag_ && tag_->erased == &obj_detail::tag_of<U>;
  }

  obj(const obj &o) noexcept : tag_(o.tag_) {
    std::memcpy(bytes_, o.bytes_, sizeof bytes_);
    if (auto *b = counted_block())
      b->retain();
  }
  obj(obj &&o) noexcept : tag_(std::exchange(o.tag_, nullptr)) {
    std::memcpy(bytes_, o.bytes_, sizeof bytes_);
  }
  obj &operator=(const obj &o) noexcept {
    obj copy(o);
    swap(copy);
    return *this;
  }
  obj &operator=(obj &&o) noexcept {
    obj taken(std::move(o));
    swap(taken);
    return *this;
  }
  ~obj() { release(); }

  void swap(obj &o) noexcept {
    std::swap(tag_, o.tag_);
    std::uintptr_t tmp[1];
    std::memcpy(tmp, bytes_, sizeof bytes_);
    std::memcpy(bytes_, o.bytes_, sizeof bytes_);
    std::memcpy(o.bytes_, tmp, sizeof bytes_);
  }
  void reset() noexcept {
    release();
    tag_ = nullptr;
  }
  // [crane::release_into]: what this holds released into [h], this empty.
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (auto *b = counted_block())
      b->release_into(h);
    tag_ = nullptr;
  }
  // [crane::make_immortal]: the box or the counted word, and what it holds.
  void make_immortal() const noexcept {
    if (boxed()) tag_->immortalize(box_);
    else if (tag_ && tag_->counted) tag_->immortalize(bytes_);
  }

  bool has_value() const noexcept { return tag_ != nullptr; }
  const std::type_info &type() const noexcept {
    return tag_ ? tag_->info : typeid(void);
  }
};

// The held value, or null when [o] is empty or holds another type.
template <class T> const T *any_cast(const obj *o) noexcept {
  using U = std::remove_cv_t<T>;
  if (!o || !o->tag_ || o->tag_->held != &obj_detail::tag_of<U>)
    return nullptr;
  if constexpr (obj_detail::held_in_place<U>)
    return std::launder(reinterpret_cast<const U *>(o->bytes_));
  else
    return &static_cast<const obj_detail::box<U> *>(o->box_)->value;
}
template <class T> T *any_cast(obj *o) noexcept {
  return const_cast<T *>(any_cast<T>(static_cast<const obj *>(o)));
}

namespace obj_detail {
// A read at the instantiation code that erased a type's parameters reads a
// counted word at may find another instantiation boxed as itself (see
// [obj::viewed_as]) and build the value it asks for, so such a read hands
// out a value: the count bump a reference would have saved.
template <class U>
inline constexpr bool read_by_value = held_handle<U> && all_obj<U, obj>::value;
template <class U> using lvalue_read_t = std::conditional_t<read_by_value<U>, U, const U &>;
} // namespace obj_detail

// From an lvalue: a reference into the box.
template <class T>
obj_detail::lvalue_read_t<std::remove_cvref_t<T>> any_cast(const obj &o) {
  using U = std::remove_cvref_t<T>;
  if (auto *p = any_cast<U>(&o))
    return *p;
  if constexpr (obj_detail::read_by_value<U>)
    return o.template read_erased<U>();
  else
    throw std::bad_any_cast();
}
template <class T> obj_detail::lvalue_read_t<std::remove_cvref_t<T>> any_cast(obj &o) {
  return any_cast<T>(static_cast<const obj &>(o));
}

// From an rvalue: a value, since the box may die with the handle.
template <class T> std::remove_cvref_t<T> any_cast(obj &&o) {
  using U = std::remove_cvref_t<T>;
  auto *p = any_cast<U>(static_cast<obj *>(&o));
  if (!p) {
    if constexpr (obj_detail::read_by_value<U>)
      return o.template read_erased<U>();
    else
      throw std::bad_any_cast();
  }
  if constexpr (obj_detail::held_handle<U>)
    return std::move(*p); // the handle is this one's own
  else if constexpr (!obj_detail::held_inline<U>)
    if (o.box_->rc.sole())
      return std::move(*p);
  return *p;
}

CRANE_RC_POLICY_END

// rebind_t<F, X>: a carrier written at the erased element, read at X.
//
// A type-constructor parameter an inductive or alias declares plain -- one
// its definition applies only at variables, [wrapped F A]'s [F] -- is given
// the carrier at the erased element ([std::optional<crane::obj>]) where it is
// a type constructor, and the family's own struct ([AE]) where it is an event
// family, whose index its struct already leaves out.  Applying it replaces the
// erased element by the argument, which is the identity on a family.
//
// Only an erased element *inside* the carrier is the element: a bare
// [crane::obj] is a family erased whole, and applied it stays erased.  So is
// a type parameterised by families ([crane_family_tag]): its erased index is
// the family's own, not an element.
template <class T>
concept family_carrier = requires { typename T::crane_family_tag; };
template <class T, class X> struct rebind_element { using type = T; };
template <class X> struct rebind_element<obj, X> { using type = X; };
template <template <class...> class Tm, class... A, class X>
  requires(!family_carrier<Tm<A...>>)
struct rebind_element<Tm<A...>, X> {
  using type = Tm<typename rebind_element<A, X>::type...>;
};
template <class R, class... A, class X> struct rebind_element<R(A...), X> {
  using type = typename rebind_element<R, X>::type(
      typename rebind_element<A, X>::type...);
};
template <class F, class X> struct rebind { using type = F; };
template <template <class...> class Tm, class... A, class X>
  requires(!family_carrier<Tm<A...>>)
struct rebind<Tm<A...>, X> {
  using type = typename rebind_element<Tm<A...>, X>::type;
};
template <class F, class X> using rebind_t = typename rebind<F, X>::type;

// constant_tc<T>::c: the type function that ignores its argument -- the
// carrier [fun _ => T], which has no template of its own to name.
template <class T> struct constant_tc {
  template <class> using c = T;
};

} // namespace crane
