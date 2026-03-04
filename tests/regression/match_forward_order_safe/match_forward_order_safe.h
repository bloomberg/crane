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

struct MatchForwardOrderSafe {
  enum class token { A, B };

  template <typename T1>
  static T1 token_rect(const T1 f, const T1 f0, const token t) {
    return [&](void) {
      switch (t) {
      case token::A: {
        return f;
      }
      case token::B: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 token_rec(const T1 f, const T1 f0, const token t) {
    return [&](void) {
      switch (t) {
      case token::A: {
        return f;
      }
      case token::B: {
        return f0;
      }
      }
    }();
  }

  static token choose(const bool b);

  static unsigned int encode(const token x);

  static inline const unsigned int t = encode(choose(false));
};
