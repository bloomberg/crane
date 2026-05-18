#ifndef INCLUDED_BOOL_OPS
#define INCLUDED_BOOL_OPS

struct BoolOps {
  static inline const bool bool_true = true;
  static inline const bool bool_false = false;
  static bool my_negb(bool b);
  static bool my_andb(bool a, bool b);
  static bool my_orb(bool a, bool b);
  static bool my_xorb(bool a, bool b);
  static uint64_t if_nat(bool b, uint64_t t, uint64_t f);
  static bool complex_bool(bool a, bool b, bool c);
  static bool nat_eq(uint64_t _x0, uint64_t _x1);
  static bool nat_lt(uint64_t _x0, uint64_t _x1);
  static bool nat_le(uint64_t _x0, uint64_t _x1);
  static inline const bool test_neg_t = my_negb(true);
  static inline const bool test_neg_f = my_negb(false);
  static inline const bool test_and_tt = my_andb(true, true);
  static inline const bool test_and_tf = my_andb(true, false);
  static inline const bool test_or_ff = my_orb(false, false);
  static inline const bool test_or_ft = my_orb(false, true);
  static inline const bool test_xor_tt = my_xorb(true, true);
  static inline const bool test_xor_tf = my_xorb(true, false);
  static inline const uint64_t test_if_t =
      if_nat(true, UINT64_C(5), UINT64_C(3));
  static inline const uint64_t test_if_f =
      if_nat(false, UINT64_C(5), UINT64_C(3));
  static inline const bool test_complex = complex_bool(true, false, true);
  static inline const bool test_eq_tt = nat_eq(UINT64_C(5), UINT64_C(5));
  static inline const bool test_eq_tf = nat_eq(UINT64_C(5), UINT64_C(3));
  static inline const bool test_lt = nat_lt(UINT64_C(3), UINT64_C(5));
};

#endif // INCLUDED_BOOL_OPS
