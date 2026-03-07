#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct JcnConditionNonzeroGate {
  struct state {
    unsigned int acc;
    bool carry;
    bool test_pin;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static bool carry(const std::shared_ptr<state> &s);

  static bool test_pin(const std::shared_ptr<state> &s);

  static bool jcn_condition(const std::shared_ptr<state> &s,
                            const unsigned int cond);

  static inline const bool t = jcn_condition(
      std::make_shared<state>(state{(((0 + 1) + 1) + 1), false, true}),
      ((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
       1));
};
