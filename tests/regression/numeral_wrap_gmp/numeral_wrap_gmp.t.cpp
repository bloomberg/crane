#include <numeral_wrap_gmp.h>

#include <cassert>

int main() {
  assert(NumeralWrapGmp::two62 == mpz_class("4611686018427387904"));
  assert(NumeralWrapGmp::two63 == mpz_class("9223372036854775808"));
  assert(NumeralWrapGmp::two64 == mpz_class("18446744073709551616"));
  assert(NumeralWrapGmp::two64_1 == mpz_class("18446744073709551617"));
  assert(NumeralWrapGmp::two128 ==
         mpz_class("340282366920938463463374607431768211456"));
  assert(NumeralWrapGmp::neg64 == mpz_class("-18446744073709551616"));
  return 0;
}
