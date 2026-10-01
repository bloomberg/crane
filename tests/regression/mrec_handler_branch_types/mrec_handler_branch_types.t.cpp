#include <mrec_handler_branch_types.h>

#include <cassert>
#include <iostream>

int main() {
  // den 2: Call 2 goes through the fmap branch, ext_call 2 = Ret 3, so inr 3.
  assert(MrecHandlerBranchTypes::is_three);
  std::cout << "mrec_handler_branch_types: ok" << std::endl;
  return 0;
}
