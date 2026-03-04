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

struct MkstateSignatureDriftSafe {
  enum class state { S0, S1 };

  template <typename T1>
  static T1 state_rect(const T1 f, const T1 f0, const state s) {
    return [&](void) {
      switch (s) {
      case state::S0: {
        return f;
      }
      case state::S1: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 state_rec(const T1 f, const T1 f0, const state s) {
    return [&](void) {
      switch (s) {
      case state::S0: {
        return f;
      }
      case state::S1: {
        return f0;
      }
      }
    }();
  }

  static unsigned int score(const state x);

  static inline const unsigned int t = (score(state::S0) + score(state::S1));
};
