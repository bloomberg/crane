#ifndef INCLUDED_SWITCH_DEFAULT_READS_BINDING
#define INCLUDED_SWITCH_DEFAULT_READS_BINDING

#include <type_traits>
#include <utility>
#include <variant>

/// A binding read only in a switch's default arm: dead-binding removal
/// must see the arm, or the declaration goes and the arm names nothing.
struct SwitchDefaultReadsBinding {
  enum class Color { RED, GREEN, BLUE, BLACK };

  template <typename T1>
  static T1 color_rect(T1 f, T1 f0, T1 f1, T1 f2, Color c) {
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
    case Color::BLACK: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(T1 f, T1 f0, T1 f1, T1 f2, Color c) {
    return color_rect<T1>(std::move(f), std::move(f0), std::move(f1),
                          std::move(f2), c);
  }

  struct shade {
    // DATA
    Color a;
    Color b;

    // ACCESSORS
    shade clone() const { return {a, b}; }

    // CREATORS
    static shade shade0(Color a, Color b) { return {a, b}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const Color &, const Color &>
  static T1 shade_rect(F0 &&f, const shade &s) {
    const auto &[a0, b0] = s;
    return f(a0, b0);
  }

  template <typename T1, typename F0>
  static T1 shade_rec(F0 &&f, const shade &s) {
    return shade_rect<T1>(f, s);
  }

  static shade pick(Color c);
};

#endif // INCLUDED_SWITCH_DEFAULT_READS_BINDING
