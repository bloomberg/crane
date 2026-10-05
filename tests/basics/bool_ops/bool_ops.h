#ifndef INCLUDED_BOOL_OPS
#define INCLUDED_BOOL_OPS

#include <cstdint>

struct BoolOps {
  static constexpr bool bool_true = true;
  static constexpr bool bool_false = false;
  static bool my_negb(bool b);
  static bool my_andb(bool a, bool b);
  static bool my_orb(bool a, bool b);
  static bool my_xorb(bool a, bool b);
  static uint64_t if_nat(bool b, uint64_t t, uint64_t f);
  static bool complex_bool(bool a, bool b, bool c);
  static bool nat_eq(uint64_t x0_, uint64_t x1_);
  static bool nat_lt(uint64_t x0_, uint64_t x1_);
  static bool nat_le(uint64_t x0_, uint64_t x1_);
  static constexpr bool test_neg_t = false;
  static constexpr bool test_neg_f = true;
  static constexpr bool test_and_tt = true;
  static constexpr bool test_and_tf = false;
  static constexpr bool test_or_ff = false;
  static constexpr bool test_or_ft = true;
  static constexpr bool test_xor_tt = false;
  static constexpr bool test_xor_tf = true;
  static constexpr uint64_t test_if_t = UINT64_C(5);
  static constexpr uint64_t test_if_f = UINT64_C(3);
  static constexpr bool test_complex = false;
  static constexpr bool test_eq_tt = true;
  static constexpr bool test_eq_tf = false;
  static constexpr bool test_lt = true;
};

#endif // INCLUDED_BOOL_OPS
