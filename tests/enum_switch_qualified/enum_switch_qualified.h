#ifndef INCLUDED_ENUM_SWITCH_QUALIFIED
#define INCLUDED_ENUM_SWITCH_QUALIFIED

#include <utility>

struct EnumSwitchQualified {
  struct Outer {
    enum class Color { RED, BLUE };

    template <typename T1> static T1 color_rect(T1 f, T1 f0, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      }
      case Color::BLUE: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 color_rec(T1 f, T1 f0, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      }
      case Color::BLUE: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    static Color flip(Color c);
    static uint64_t code(Color c);
  };

  static inline const uint64_t t = Outer::code(Outer::flip(Outer::Color::RED));
};

#endif // INCLUDED_ENUM_SWITCH_QUALIFIED
