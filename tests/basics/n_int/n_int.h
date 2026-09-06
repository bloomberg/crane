#ifndef INCLUDED_N_INT
#define INCLUDED_N_INT

#include <utility>

struct Pos {
  static unsigned int add_carry(unsigned int x, unsigned int y);
};

struct NIntTest {
  static unsigned int add_test(unsigned int x0_, unsigned int x1_);
  static unsigned int mul_test(unsigned int x0_, unsigned int x1_);
  static unsigned int sub_test(unsigned int x0_, unsigned int x1_);
  static unsigned int div_test(unsigned int x0_, unsigned int x1_);
  static bool eqb_test(unsigned int x0_, unsigned int x1_);
  static bool ltb_test(unsigned int x0_, unsigned int x1_);
  static bool leb_test(unsigned int x0_, unsigned int x1_);
  static unsigned int succ_test(unsigned int x0_);
  static unsigned int pred_test(unsigned int x0_);
  static unsigned int double_test(unsigned int x0_);
  static inline const unsigned int zero_val = 0u;
  static inline const unsigned int five_val = 5u;
  static inline const unsigned int big_val = 1000u;
  static bool is_zero(unsigned int n);
  static unsigned int pos_add(unsigned int x0_, unsigned int x1_);
  static unsigned int pos_succ(unsigned int x0_);
};

#endif // INCLUDED_N_INT
