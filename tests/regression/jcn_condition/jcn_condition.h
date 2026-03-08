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

struct JcnCondition {
  struct state {
    unsigned int acc;
    bool carry;
    bool test_pin;
  };

  static bool jcn_condition(const std::shared_ptr<state> &s,
                            const unsigned int cond);

  static inline const bool check_carry_clear_gate =
      jcn_condition(std::make_shared<state>(state{1u, false, true}), 10u);

  static inline const bool check_nonzero_gate =
      jcn_condition(std::make_shared<state>(state{3u, false, true}), 12u);

  static inline const bool check_test_high =
      jcn_condition(std::make_shared<state>(state{1u, false, true}), 9u);

  static inline const bool check_test_low =
      jcn_condition(std::make_shared<state>(state{1u, false, false}), 1u);

  static inline const bool check_zero_gate =
      jcn_condition(std::make_shared<state>(state{0u, false, true}), 4u);

  static inline const bool t =
      (check_carry_clear_gate &&
       (check_nonzero_gate &&
        (check_test_high && (check_test_low && check_zero_gate))));
};
