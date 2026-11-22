#include <deque_fold_curried_acc.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = DequeFoldCurriedAcc::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 6);
  return 0;
}
