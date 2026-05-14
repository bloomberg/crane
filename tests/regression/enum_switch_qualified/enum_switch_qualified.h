#ifndef INCLUDED_ENUM_SWITCH_QUALIFIED
#define INCLUDED_ENUM_SWITCH_QUALIFIED

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

struct EnumSwitchQualified {
  struct Outer {
    enum class Color { e_RED, e_BLUE };

    template <typename T1> static T1 color_rect(T1 f, T1 f0, const Color c) {
      switch (c) {
      case Color::e_RED: {
        return f;
      }
      case Color::e_BLUE: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 color_rec(T1 f, T1 f0, const Color c) {
      switch (c) {
      case Color::e_RED: {
        return f;
      }
      case Color::e_BLUE: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    static Color flip(const Color c);
    static unsigned int code(const Color c);
  };

  static inline const unsigned int t =
      Outer::code(Outer::flip(Outer::Color::e_RED));
};

#endif // INCLUDED_ENUM_SWITCH_QUALIFIED
