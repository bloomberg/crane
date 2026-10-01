#ifndef INCLUDED_LOCAL_FIXPOINT
#define INCLUDED_LOCAL_FIXPOINT

#include "fn.h"
#include <utility>
#include <variant>

struct Monadic {
  template <typename s, typename a> using State = crane::fn<std::pair<a, s>(s)>;

  template <typename T1, typename T2> static State<T1, T2> state_return(T2 x) {
    return [=](const T1 &s) { return std::make_pair(x, s); };
  }

  template <typename T1, typename T2, typename T3>
  static State<T1, T3>
  state_bind(std::type_identity_t<State<T1, T2>> ma,
             std::type_identity_t<crane::fn<State<T1, T3>(T2)>> f) {
    return [=](const T1 &s) {
      auto [a, s_] = ma(s);
      return f(a)(s_);
    };
  }

  static State<bool, std::monostate> foo_state(std::monostate _x);
  static inline const bool foo = []() {
    crane::fn<State<bool, std::monostate>(std::monostate)> foo_state_ =
        [](std::monostate u) {
          return state_bind<bool, std::monostate, std::monostate>(
              foo_state(u), [](std::monostate) {
                return state_return<bool, std::monostate>(std::monostate{});
              });
        };
    auto [_x, a] = foo_state_(std::monostate{})(true);
    return a;
  }();
};

#endif // INCLUDED_LOCAL_FIXPOINT
