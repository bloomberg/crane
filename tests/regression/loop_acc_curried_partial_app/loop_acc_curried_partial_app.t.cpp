#include <loop_acc_curried_partial_app.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LoopAccCurriedPartialApp::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 1);
  return 0;
}
