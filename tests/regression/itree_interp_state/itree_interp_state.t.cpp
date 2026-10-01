#include <itree_interp_state.h>

#include <cassert>
#include <iostream>

int main() {
  // state 1: first Get answers 1, second answers 2; result 1 + 2 = 3.
  assert(ItreeInterpState::is_three);
  std::cout << "itree_interp_state: ok" << std::endl;
  return 0;
}
