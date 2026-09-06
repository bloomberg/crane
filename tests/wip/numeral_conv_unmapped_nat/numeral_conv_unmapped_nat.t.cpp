#include <numeral_conv_unmapped_nat.h>
#include <iostream>
int main() {
  std::cout << NumeralConvUnmappedNat::run << std::endl;
  return NumeralConvUnmappedNat::run == 16 ? 0 : 1;
}
