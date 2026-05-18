#ifndef INCLUDED_N_INT
#define INCLUDED_N_INT

#include <utility>

struct Pos {
  static unsigned int add_carry(unsigned int x, unsigned int y);
};

struct NIntTest {
  static unsigned int add_test(unsigned int _x0, unsigned int _x1);
  static unsigned int mul_test(unsigned int _x0, unsigned int _x1);
  static unsigned int sub_test(unsigned int _x0, unsigned int _x1);
  static unsigned int div_test(unsigned int _x0, unsigned int _x1);
  static bool eqb_test(unsigned int _x0, unsigned int _x1);
  static bool ltb_test(unsigned int _x0, unsigned int _x1);
  static bool leb_test(unsigned int _x0, unsigned int _x1);
  static unsigned int succ_test(unsigned int _x0);
  static unsigned int pred_test(unsigned int _x0);
  static unsigned int double_test(unsigned int _x0);
  static inline const unsigned int zero_val = 0u;
  static inline const unsigned int five_val = 5u;
  static inline const unsigned int big_val = 1000u;
  static bool is_zero(unsigned int n);
  static unsigned int pos_add(unsigned int _x0, unsigned int _x1);
  static unsigned int pos_succ(unsigned int _x0);
};

#endif // INCLUDED_N_INT
