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

struct EnumSwitchColorFlip {
  struct Outer {
    enum class color { Red, Blue };

    template <typename T1>
    static T1 color_rect(const T1 f, const T1 f0, const color c) {
      return [&](void) {
        switch (c) {
        case color::Red: {
          return f;
        }
        case color::Blue: {
          return f0;
        }
        }
      }();
    }

    template <typename T1>
    static T1 color_rec(const T1 f, const T1 f0, const color c) {
      return [&](void) {
        switch (c) {
        case color::Red: {
          return f;
        }
        case color::Blue: {
          return f0;
        }
        }
      }();
    }

    static color flip(const color c);

    static unsigned int code(const color c);
  };

  static inline const unsigned int t =
      Outer::code(Outer::flip(Outer::color::Red));
};
