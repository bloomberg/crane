#include <snd_pair_poly_sum_scrutinee.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = SndPairPolySumScrutinee::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 2);
  return 0;
}
