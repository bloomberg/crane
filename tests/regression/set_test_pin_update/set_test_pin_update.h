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

struct SetTestPinUpdate {
  struct state {
    unsigned int acc;
    bool test_pin;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static bool test_pin(const std::shared_ptr<state> &s);

  static std::shared_ptr<state> set_test_pin(std::shared_ptr<state> s,
                                             const bool v);

  static inline const unsigned int t = []() {
    return [](void) {
      std::shared_ptr<state> s_ =
          set_test_pin(std::make_shared<state>(
                           state{((((((0 + 1) + 1) + 1) + 1) + 1) + 1), false}),
                       true);
      return (s_->acc + [&](void) {
        if (s_->test_pin) {
          return (0 + 1);
        } else {
          return 0;
        }
      }());
    }();
  }();
};
