#include <bde_loop_acc_fn_std_string.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = BdeLoopAccFnStdString::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 1);
  return 0;
}
