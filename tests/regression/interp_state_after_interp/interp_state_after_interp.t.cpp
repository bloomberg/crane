#include <interp_state_after_interp.h>

#include <cassert>
#include <iostream>

int main() {
  // Get answered with 1, then Out 1 is re-raised in the target family.
  assert(InterpStateAfterInterp::is_one);
  std::cout << "interp_state_after_interp: ok" << std::endl;
  return 0;
}
