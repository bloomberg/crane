#ifndef INCLUDED_JCN_OPS
#define INCLUDED_JCN_OPS

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
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct JcnOps {
  struct state {
    unsigned int acc;
    bool carry;
    bool test_pin;
    unsigned int pc;
  };

  __attribute__((pure)) static bool
  jcn_condition(const std::shared_ptr<state> &s, const unsigned int cond);
  __attribute__((pure)) static unsigned int addr12_of_nat(const unsigned int n);
  __attribute__((pure)) static unsigned int
  pc_inc2(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int page_of(const unsigned int p);
  __attribute__((pure)) static unsigned int page_base(const unsigned int p);
  __attribute__((pure)) static unsigned int
  base_for_next2(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int
  branch_target(const std::shared_ptr<state> &s, const unsigned int cond,
                const unsigned int off);
  static inline const unsigned int test_branch_target = branch_target(
      std::make_shared<state>(state{0u, true, false, 300u}), 2u, 17u);
  static inline const bool check_carry_clear_gate =
      jcn_condition(std::make_shared<state>(state{1u, false, true, 0u}), 10u);
  static inline const bool check_nonzero_gate =
      jcn_condition(std::make_shared<state>(state{3u, false, true, 0u}), 12u);
  static inline const bool check_test_high =
      jcn_condition(std::make_shared<state>(state{1u, false, true, 0u}), 9u);
  static inline const bool check_test_low =
      jcn_condition(std::make_shared<state>(state{1u, false, false, 0u}), 1u);
  static inline const bool check_zero_gate =
      jcn_condition(std::make_shared<state>(state{0u, false, true, 0u}), 4u);
  static inline const bool test_condition =
      (check_carry_clear_gate &&
       (check_nonzero_gate &&
        (check_test_high && (check_test_low && check_zero_gate))));
  static inline const unsigned int JCN_JNT = 1u;
  static inline const unsigned int JCN_JC = 2u;
  static inline const unsigned int JCN_JZ = 4u;
  static inline const unsigned int JCN_JT = 9u;
  static inline const unsigned int JCN_JNC = 10u;
  static inline const unsigned int JCN_JNZ = 12u;
  static inline const unsigned int test_constants = []() {
    return [](void) {
      std::shared_ptr<state> s =
          std::make_shared<state>(state{0u, true, false, 0u});
      return (([&](void) {
                if (jcn_condition(s, JCN_JC)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }() +
               [&](void) {
                 if (jcn_condition(s, JCN_JZ)) {
                   return 1u;
                 } else {
                   return 0u;
                 }
               }()) +
              [&](void) {
                if (jcn_condition(s, JCN_JNT)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }());
    }();
  }();
  static inline const std::pair<std::pair<unsigned int, bool>, unsigned int> t =
      std::make_pair(std::make_pair(test_branch_target, test_condition),
                     test_constants);
};

#endif // INCLUDED_JCN_OPS
