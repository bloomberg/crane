#ifndef INCLUDED_LET_MATCH_TYPE
#define INCLUDED_LET_MATCH_TYPE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct LetMatchType {
  /// 1. let-bound bool match returning nat
  __attribute__((pure)) static unsigned int let_match_nat(const bool &b);
  /// 2. let-bound nat match returning string — TRIGGERS std::any bug
  __attribute__((pure)) static std::string
  let_match_string(const unsigned int &n);
  /// 3. let-bound option match
  __attribute__((pure)) static unsigned int
  let_match_option(const std::optional<unsigned int> &o);
  /// 4. let-bound nested bool match
  __attribute__((pure)) static unsigned int let_nested_bool(const bool &a,
                                                            const bool &b);
  /// 5. Multiple let-bound matches
  __attribute__((pure)) static unsigned int multi_let_match(const bool &a,
                                                            const bool &b);
  /// 6. let-bound match used in function argument
  __attribute__((pure)) static unsigned int
  let_match_in_arg(const unsigned int &n);
  /// 7. let-bound match in monadic context
  static std::string let_match_monadic(const bool &b);
  /// 8. let-bound match of custom type
  enum class Direction { e_NORTH, e_SOUTH, e_EAST, e_WEST };

  template <typename T1>
  static T1 direction_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const Direction d) {
    switch (d) {
    case Direction::e_NORTH: {
      return f;
    }
    case Direction::e_SOUTH: {
      return f0;
    }
    case Direction::e_EAST: {
      return f1;
    }
    case Direction::e_WEST: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 direction_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                          const Direction d) {
    switch (d) {
    case Direction::e_NORTH: {
      return f;
    }
    case Direction::e_SOUTH: {
      return f0;
    }
    case Direction::e_EAST: {
      return f1;
    }
    case Direction::e_WEST: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  direction_offset(const Direction d);
};

#endif // INCLUDED_LET_MATCH_TYPE
