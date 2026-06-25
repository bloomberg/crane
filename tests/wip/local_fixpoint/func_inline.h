#ifndef INCLUDED_FUNC_INLINE
#define INCLUDED_FUNC_INLINE

#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

struct Monadic {
  template <typename s, typename a>
  using State = std::function<std::pair<a, s>(s)>;

  template <typename T1, typename T2> static State<T1, T2> state_return(T2 x) {
    return [=](T1 s) mutable { return std::make_pair(x, s); };
  }

  template <typename T1, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<State<T1, T3>, F1 &, T2 &>
  static State<T1, T3> state_bind(State<T1, T2> ma, F1 &&f) {
    return [=](const T1 &s) mutable {
      auto _cs = ma(s);
      T2 a = std::move(_cs.first);
      T1 s_ = std::move(_cs.second);
      return f(a)(s_);
    };
  }

  static State<bool, std::monostate> foo_state(std::monostate _x);
  static inline const bool foo = []() {
    std::function<std::pair<std::monostate, bool>(std::monostate, bool)>
        foo_state_ = [](std::monostate u) {
          return state_bind<bool, std::monostate, std::monostate>(
              foo_state(u), [](std::monostate) {
                return state_return<bool, std::monostate>(std::monostate{});
              });
        };
    auto _cs = foo_state_(std::monostate{}, true);
    std::monostate _x = std::move(_cs.first);
    bool a = std::move(_cs.second);
    return a;
  }();
};

#endif // INCLUDED_FUNC_INLINE
