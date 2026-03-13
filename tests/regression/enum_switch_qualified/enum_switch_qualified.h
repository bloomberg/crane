#ifndef INCLUDED_ENUM_SWITCH_QUALIFIED
#define INCLUDED_ENUM_SWITCH_QUALIFIED

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EnumSwitchQualified {
  struct Outer {
    enum class Color { e_RED, e_BLUE };

    template <typename T1>
    static T1 color_rect(const T1 f, const T1 f0, const Color c) {
      return [&](void) {
        switch (c) {
        case Color::e_RED: {
          return f;
        }
        case Color::e_BLUE: {
          return f0;
        }
        }
      }();
    }

    template <typename T1>
    static T1 color_rec(const T1 f, const T1 f0, const Color c) {
      return [&](void) {
        switch (c) {
        case Color::e_RED: {
          return f;
        }
        case Color::e_BLUE: {
          return f0;
        }
        }
      }();
    }

    __attribute__((pure)) static Color flip(const Color c);
    __attribute__((pure)) static unsigned int code(const Color c);
  };

  static inline const unsigned int t =
      Outer::code(Outer::flip(Outer::Color::e_RED));
};

#endif // INCLUDED_ENUM_SWITCH_QUALIFIED
