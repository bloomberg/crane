#include <self_comparison_mapped_werror.h>

#include <cstdint>
#include <iostream>

#define M SelfComparisonMappedWerror

int main() {
  int fails = 0;
  if (!(M::z_ge_self(4) == true)) { std::cout << "FAIL: M::z_ge_self(4)" << std::endl; ++fails; }
  if (!(M::z_gt_self(4) == false)) { std::cout << "FAIL: M::z_gt_self(4)" << std::endl; ++fails; }
  if (!(M::i_eq_self(4) == true)) { std::cout << "FAIL: M::i_eq_self(4)" << std::endl; ++fails; }
  if (!(M::i_le_self(4) == true)) { std::cout << "FAIL: M::i_le_self(4)" << std::endl; ++fails; }
  if (!(M::i_lt_self(4) == false)) { std::cout << "FAIL: M::i_lt_self(4)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All self_comparison_mapped_werror tests passed!" << std::endl;
  return fails;
}
