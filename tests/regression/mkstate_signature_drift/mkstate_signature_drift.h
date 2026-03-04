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

struct MkstateSignatureDrift {
  enum class item { S_, S_0 };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const item i) {
    return [&](void) {
      switch (i) {
      case item::S_: {
        return f;
      }
      case item::S_0: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 item_rec(const T1 f, const T1 f0, const item i) {
    return [&](void) {
      switch (i) {
      case item::S_: {
        return f;
      }
      case item::S_0: {
        return f0;
      }
      }
    }();
  }

  static unsigned int score(const item x);

  static inline const unsigned int t = (score(item::S_) + score(item::S_0));
};
