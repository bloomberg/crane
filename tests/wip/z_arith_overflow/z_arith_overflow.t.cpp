#include <z_arith_overflow.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // Verify intermediate value is correct
  auto big = ZArithOverflow::big_z;
  std::cout << "big_z = " << big << std::endl;
  assert(big == INT64_C(3100000000));

  // 3,100,000,000^2 = 9,610,000,000,000,000,000 > INT64_MAX
  // In Rocq: fine (Z is arbitrary precision, result is positive)
  // In C++: signed multiplication overflow is UB; result wraps negative
  auto product = ZArithOverflow::overflow_mul;
  std::cout << "overflow_mul = " << product << std::endl;
  // In Rocq, product of two positive values is always positive
  assert(product > 0);

  // is_positive should be true (product of positives)
  auto pos = ZArithOverflow::is_positive;
  std::cout << "is_positive = " << pos << std::endl;
  assert(pos == true);

  return 0;
}
