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
// in the handle itself; anything else lives in one intrusive-counted heap
// box, and copying the handle bumps the count.
//
// Reading a value back is [crane::any_cast], with [std::any_cast]'s
// signature and one difference that follows from sharing: from an lvalue
// handle it hands out a [const T &] into the box instead of a copy, and from
// an rvalue handle it returns a [T] -- moved out when the handle was the
// box's only owner, copied otherwise -- so no reference outlives its box.
// Reading at the wrong type throws [std::bad_any_cast].
#pragma once
#include <any>
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
inline constexpr bool held_inline = std::is_trivially_copyable_v<T> &&
                                    sizeof(T) <= sizeof(void *) &&
                                    alignof(T) <= alignof(void *);

template <class T> struct box : shared_block, pool_detail::pooled<box<T>> {
  T value;
  template <class... A>
  explicit box(A &&...a)
      : shared_block{{}, &drop}, value(std::forward<A>(a)...) {}
  static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
    box::dispose(static_cast<const box *>(static_cast<const shared_block *>(b)), h);
  }
};

// One per held type: what the handle's tag points at.
struct type_tag {
  const std::type_info &info;
  bool inline_;
};
template <class T>
inline constexpr type_tag tag_of{typeid(T), held_inline<T>};

} // namespace obj_detail

class obj {
public:
  // A copy is a refcount bump, or a word's copy (see field.h).
  using crane_cheap_copy = void;

private:
  const obj_detail::type_tag *tag_ = nullptr;
  union {
    const shared_block *box_;
    alignas(void *) unsigned char bytes_[sizeof(void *)];
  };

  bool boxed() const noexcept { return tag_ && !tag_->inline_; }
  void retain() const noexcept {
    if (boxed())
      box_->retain();
  }
  void release() noexcept {
    if (boxed())
      box_->release();
  }

  template <class T> friend const T *any_cast(const obj *) noexcept;
  template <class T> friend T *any_cast(obj *) noexcept;
  template <class T> friend std::remove_cvref_t<T> any_cast(obj &&);

public:
  obj() noexcept : box_(nullptr) {}

  template <class V, class T = std::decay_t<V>>
    requires(!std::is_same_v<T, obj> && std::is_copy_constructible_v<T>)
  obj(V &&v) : tag_(&obj_detail::tag_of<T>) {
    if constexpr (obj_detail::held_inline<T>)
      ::new (static_cast<void *>(bytes_)) T(std::forward<V>(v));
    else
      box_ = new obj_detail::box<T>(std::forward<V>(v));
  }

  obj(const obj &o) noexcept : tag_(o.tag_) {
    std::memcpy(bytes_, o.bytes_, sizeof bytes_);
    retain();
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
    unsigned char tmp[sizeof bytes_];
    std::memcpy(tmp, bytes_, sizeof bytes_);
    std::memcpy(bytes_, o.bytes_, sizeof bytes_);
    std::memcpy(o.bytes_, tmp, sizeof bytes_);
  }
  void reset() noexcept {
    release();
    tag_ = nullptr;
  }

  bool has_value() const noexcept { return tag_ != nullptr; }
  const std::type_info &type() const noexcept {
    return tag_ ? tag_->info : typeid(void);
  }
};

// The held value, or null when [o] is empty or holds another type.
template <class T> const T *any_cast(const obj *o) noexcept {
  using U = std::remove_cv_t<T>;
  if (!o || o->tag_ != &obj_detail::tag_of<U>)
    return nullptr;
  if constexpr (obj_detail::held_inline<U>)
    return std::launder(reinterpret_cast<const U *>(o->bytes_));
  else
    return &static_cast<const obj_detail::box<U> *>(o->box_)->value;
}
template <class T> T *any_cast(obj *o) noexcept {
  return const_cast<T *>(any_cast<T>(static_cast<const obj *>(o)));
}

// From an lvalue: a reference into the box.
template <class T>
const std::remove_cvref_t<T> &any_cast(const obj &o) {
  if (auto *p = any_cast<std::remove_cvref_t<T>>(&o))
    return *p;
  throw std::bad_any_cast();
}
template <class T> const std::remove_cvref_t<T> &any_cast(obj &o) {
  return any_cast<T>(static_cast<const obj &>(o));
}

// From an rvalue: a value, since the box may die with the handle.
template <class T> std::remove_cvref_t<T> any_cast(obj &&o) {
  using U = std::remove_cvref_t<T>;
  auto *p = any_cast<U>(static_cast<obj *>(&o));
  if (!p)
    throw std::bad_any_cast();
  if constexpr (!obj_detail::held_inline<U>)
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

} // namespace crane
