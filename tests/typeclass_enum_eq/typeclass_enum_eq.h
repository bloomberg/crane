#ifndef INCLUDED_TYPECLASS_ENUM_EQ
#define INCLUDED_TYPECLASS_ENUM_EQ

#include <concepts>
#include <utility>

template <typename I, typename A>
concept Eq = requires {
  { I::eqb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};

struct TypeclassEnumEq {
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static bool color_eqb(Color x, Color y);

  struct ColorEq {
    constexpr static bool eqb(Color a0, Color a1) { return color_eqb(a0, a1); }
  };

  static_assert(Eq<ColorEq, Color>);

  template <typename _tcI0, typename T1>
    requires Eq<_tcI0, T1>
  static bool is_equal(const T1 &x, const T1 &y) {
    return _tcI0::eqb(x, y);
  }

  static inline const bool test_same =
      is_equal<ColorEq, Color>(Color::RED, Color::RED);
  static inline const bool test_diff =
      is_equal<ColorEq, Color>(Color::RED, Color::BLUE);
};

#endif // INCLUDED_TYPECLASS_ENUM_EQ
