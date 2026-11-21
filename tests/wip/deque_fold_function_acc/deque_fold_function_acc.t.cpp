#include <deque_fold_function_acc.h>

#include <iostream>

int main() {
  auto a = DequeFoldFunctionAcc::t_1;
  std::cout << a << std::endl;
  return a == 16 ? 0 : 1;
}
