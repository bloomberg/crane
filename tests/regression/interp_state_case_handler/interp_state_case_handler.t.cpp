#include <interp_state_case_handler.h>

#include <cassert>
#include <iostream>

int main() {
  // 0 -Inc-> 1, Get = 1, -Inc-> 2, Get = 2: 1 + 2 = 3.
  assert(InterpStateCaseHandler::is_three);
  std::cout << "interp_state_case_handler: ok" << std::endl;
  return 0;
}
