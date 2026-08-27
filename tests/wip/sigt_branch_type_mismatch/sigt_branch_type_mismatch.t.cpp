// WIP: this test does not build yet.
//
// A `sigT` over a boolean-indexed type family whose branches are `nat` and
// `nat -> nat` extracts to a single lambda whose two branches return
// `uint64_t` and `std::any`, which clang rejects.
#include "sigt_branch_type_mismatch.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigtBranchTypeMismatch::go == 8);
  std::cout << "sigt_branch_type_mismatch: go = " << SigtBranchTypeMismatch::go << " PASSED" << std::endl;
  return 0;
}
