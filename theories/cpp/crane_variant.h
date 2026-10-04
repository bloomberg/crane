// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::variant: the tagged union an inductive's alternatives are stored in
// under `Set Crane FastVariant`.
//
// It offers the part of std::variant's interface generated code uses --
// holds_alternative, get, get_if, index, emplace -- with the same meaning.
// What differs is how it copies, moves and destroys itself: an inline switch
// on its tag, where libc++'s std::variant calls through a table of function
// pointers that the optimiser does not see through.  Every copy, move and
// destruction of an extracted value goes through one of these, so on a
// program that passes values around (an interpreter, say) that indirection
// is a large share of the run time.
//
// A wrong alternative is reported as std::variant reports it, by throwing
// std::bad_variant_access.  So is the state an assignment leaves when building
// the new alternative throws: the old one is gone and no new one exists, and
// the variant holds nothing (std::variant's valueless_by_exception) rather
// than a tag naming a destroyed alternative.  Moves are noexcept exactly when
// every alternative's move is.

#ifndef INCLUDED_CRANE_VARIANT
#define INCLUDED_CRANE_VARIANT

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <new>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>

namespace crane {

template <class T, class... Ts> struct variant_index;
template <class T, class... Ts>
struct variant_index<T, T, Ts...> : std::integral_constant<std::size_t, 0> {};
template <class T, class U, class... Ts>
struct variant_index<T, U, Ts...>
    : std::integral_constant<std::size_t, 1 + variant_index<T, Ts...>::value> {};

template <class... Ts> class variant {
  static_assert(sizeof...(Ts) > 0 && sizeof...(Ts) < 255,
                "crane::variant: between 1 and 254 alternatives");

  template <std::size_t I> using alt = std::tuple_element_t<I, std::tuple<Ts...>>;

  template <class T> static constexpr bool is_alternative = (std::is_same_v<T, Ts> || ...);

  alignas(Ts...) unsigned char storage_[std::max({sizeof(Ts)...})];
  std::uint8_t index_;

  // No alternative: the index no alternative has, so every test on it fails
  // and destroy() has nothing to do.
  static constexpr std::uint8_t valueless = 255;
  static constexpr bool nothrow_move = (std::is_nothrow_move_constructible_v<Ts> && ...);

  // Replace the alternative with whatever [build] constructs, which sets
  // [index_] once it has succeeded.
  template <class Build> void rebuild(Build &&build) {
    destroy();
    index_ = valueless;
    build();
  }

  // f(integral_constant<I>) for the active index I: a chain of compares the
  // optimiser turns into a jump table, inlined where it is used.
  template <class F, std::size_t... I>
  void on_index(F &&f, std::index_sequence<I...>) const {
    (void)((index_ == I ? (f(std::integral_constant<std::size_t, I>{}), true) : false) || ...);
  }
  template <class F> void on_index(F &&f) const {
    on_index(std::forward<F>(f), std::index_sequence_for<Ts...>{});
  }

  template <std::size_t I> alt<I> &raw() {
    return *std::launder(reinterpret_cast<alt<I> *>(storage_));
  }
  template <std::size_t I> const alt<I> &raw() const {
    return *std::launder(reinterpret_cast<const alt<I> *>(storage_));
  }

  void destroy() {
    on_index([&](auto i) {
      using A = alt<decltype(i)::value>;
      if constexpr (!std::is_trivially_destructible_v<A>) raw<decltype(i)::value>().~A();
    });
  }
  void copy_from(const variant &o) {
    o.on_index([&](auto i) {
      ::new (storage_) alt<decltype(i)::value>(o.template raw<decltype(i)::value>());
    });
    index_ = o.index_;
  }
  void move_from(variant &o) {
    o.on_index([&](auto i) {
      ::new (storage_) alt<decltype(i)::value>(std::move(o.template raw<decltype(i)::value>()));
    });
    index_ = o.index_;
  }

public:
  variant() : index_(0) { ::new (storage_) alt<0>(); }
  variant(const variant &o) { copy_from(o); }
  variant(variant &&o) noexcept(nothrow_move) { move_from(o); }

  // From one of the alternatives, exactly: generated code always names the
  // alternative it builds.
  template <class T, class D = std::decay_t<T>,
            class = std::enable_if_t<is_alternative<D> && !std::is_same_v<D, variant>>>
  variant(T &&t) : index_(variant_index<D, Ts...>::value) {
    ::new (storage_) D(std::forward<T>(t));
  }

  template <std::size_t I, class... A>
  explicit variant(std::in_place_index_t<I>, A &&...a) : index_(I) {
    ::new (storage_) alt<I>(std::forward<A>(a)...);
  }

  variant &operator=(const variant &o) {
    if (this != &o)
      rebuild([&] { copy_from(o); });
    return *this;
  }
  variant &operator=(variant &&o) noexcept(nothrow_move) {
    if (this != &o)
      rebuild([&] { move_from(o); });
    return *this;
  }
  template <class T, class D = std::decay_t<T>,
            class = std::enable_if_t<is_alternative<D> && !std::is_same_v<D, variant>>>
  variant &operator=(T &&t) {
    emplace<variant_index<D, Ts...>::value>(std::forward<T>(t));
    return *this;
  }

  template <std::size_t I, class... A> alt<I> &emplace(A &&...a) {
    rebuild([&] {
      ::new (storage_) alt<I>(std::forward<A>(a)...);
      index_ = I;
    });
    return raw<I>();
  }

  ~variant() { destroy(); }

  std::size_t index() const { return index_; }

  template <class T> bool holds() const { return index_ == variant_index<T, Ts...>::value; }

  template <std::size_t I> alt<I> &at() {
    if (index_ != I) [[unlikely]]
      throw std::bad_variant_access();
    return raw<I>();
  }
  template <std::size_t I> const alt<I> &at() const {
    if (index_ != I) [[unlikely]]
      throw std::bad_variant_access();
    return raw<I>();
  }
  template <std::size_t I> alt<I> *at_if() { return index_ == I ? &raw<I>() : nullptr; }
  template <std::size_t I> const alt<I> *at_if() const {
    return index_ == I ? &raw<I>() : nullptr;
  }
};

template <class T, class... Ts> bool holds_alternative(const variant<Ts...> &v) {
  return v.template holds<T>();
}

template <std::size_t I, class... Ts> decltype(auto) get(variant<Ts...> &v) { return v.template at<I>(); }
template <std::size_t I, class... Ts> decltype(auto) get(const variant<Ts...> &v) {
  return v.template at<I>();
}
template <std::size_t I, class... Ts> decltype(auto) get(variant<Ts...> &&v) {
  return std::move(v.template at<I>());
}

template <class T, class... Ts> T &get(variant<Ts...> &v) {
  return v.template at<variant_index<T, Ts...>::value>();
}
template <class T, class... Ts> const T &get(const variant<Ts...> &v) {
  return v.template at<variant_index<T, Ts...>::value>();
}
template <class T, class... Ts> T &&get(variant<Ts...> &&v) {
  return std::move(v.template at<variant_index<T, Ts...>::value>());
}

template <class T, class... Ts> T *get_if(variant<Ts...> *v) {
  return v ? v->template at_if<variant_index<T, Ts...>::value>() : nullptr;
}
template <class T, class... Ts> const T *get_if(const variant<Ts...> *v) {
  return v ? v->template at_if<variant_index<T, Ts...>::value>() : nullptr;
}

// The same accessors on a std::variant, so code that names them matches the
// runtime's own std::variant-based types (crane_itree.h's) too.
template <class T, class... Ts> bool holds_alternative(const std::variant<Ts...> &v) {
  return std::holds_alternative<T>(v);
}
template <class T, class... Ts> T &get(std::variant<Ts...> &v) { return std::get<T>(v); }
template <class T, class... Ts> const T &get(const std::variant<Ts...> &v) {
  return std::get<T>(v);
}
template <class T, class... Ts> T &&get(std::variant<Ts...> &&v) {
  return std::get<T>(std::move(v));
}
template <class T, class... Ts> T *get_if(std::variant<Ts...> *v) { return std::get_if<T>(v); }
template <class T, class... Ts> const T *get_if(const std::variant<Ts...> *v) {
  return std::get_if<T>(v);
}

} // namespace crane

#endif // INCLUDED_CRANE_VARIANT
