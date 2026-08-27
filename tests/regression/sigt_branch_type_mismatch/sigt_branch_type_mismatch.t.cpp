// A `sigT` over a boolean-indexed type family whose branches are `nat` and
// `nat -> nat`: the erased payload is called through the erased-callable
// adapter and its result unboxed.
#include "sigt_branch_type_mismatch.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigtBranchTypeMismatch::go == 8);
  std::cout << "sigt_branch_type_mismatch: go = " << SigtBranchTypeMismatch::go << " PASSED" << std::endl;
  return 0;
}
