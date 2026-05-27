#ifndef INCLUDED_JCN_OPS
#define INCLUDED_JCN_OPS

#include <utility>

struct JcnOps {
  struct state {
    uint64_t acc;
    bool carry;
    bool test_pin;
    uint64_t pc;

    // ACCESSORS
    state clone() const {
      return state{this->acc, this->carry, this->test_pin, this->pc};
    }
  };

  static bool jcn_condition(const state &s, uint64_t cond);
  static uint64_t addr12_of_nat(uint64_t n);
  static uint64_t pc_inc2(const state &s);
  static uint64_t page_of(uint64_t p);
  static uint64_t page_base(uint64_t p);
  static uint64_t base_for_next2(const state &s);
  static uint64_t branch_target(const state &s, uint64_t cond, uint64_t off);
  static inline const uint64_t test_branch_target =
      branch_target(state{UINT64_C(0), true, false, UINT64_C(300)}, UINT64_C(2),
                    UINT64_C(17));
  static inline const bool check_carry_clear_gate =
      jcn_condition(state{UINT64_C(1), false, true, UINT64_C(0)}, UINT64_C(10));
  static inline const bool check_nonzero_gate =
      jcn_condition(state{UINT64_C(3), false, true, UINT64_C(0)}, UINT64_C(12));
  static inline const bool check_test_high =
      jcn_condition(state{UINT64_C(1), false, true, UINT64_C(0)}, UINT64_C(9));
  static inline const bool check_test_low =
      jcn_condition(state{UINT64_C(1), false, false, UINT64_C(0)}, UINT64_C(1));
  static inline const bool check_zero_gate =
      jcn_condition(state{UINT64_C(0), false, true, UINT64_C(0)}, UINT64_C(4));
  static inline const bool test_condition =
      (check_carry_clear_gate &&
       (check_nonzero_gate &&
        (check_test_high && (check_test_low && check_zero_gate))));
  static inline const uint64_t JCN_JNT = UINT64_C(1);
  static inline const uint64_t JCN_JC = UINT64_C(2);
  static inline const uint64_t JCN_JZ = UINT64_C(4);
  static inline const uint64_t JCN_JT = UINT64_C(9);
  static inline const uint64_t JCN_JNC = UINT64_C(10);
  static inline const uint64_t JCN_JNZ = UINT64_C(12);
  static inline const uint64_t test_constants = []() {
    return []() {
      state s = state{UINT64_C(0), true, false, UINT64_C(0)};
      return (
          ((jcn_condition(std::move(s), JCN_JC) ? UINT64_C(1) : UINT64_C(0)) +
           (jcn_condition(std::move(s), JCN_JZ) ? UINT64_C(1) : UINT64_C(0))) +
          (jcn_condition(std::move(s), JCN_JNT) ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
  static inline const std::pair<std::pair<uint64_t, bool>, uint64_t> t =
      std::make_pair(std::make_pair(test_branch_target, test_condition),
                     test_constants);
};

#endif // INCLUDED_JCN_OPS
