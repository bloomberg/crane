#include <deque_fold_function_acc.h>

#include <iostream>

int main() {
  auto a = DequeFoldFunctionAcc::t_1;
  auto b = DequeFoldFunctionAcc::t_2;
  std::cout << a << " " << b << std::endl;
  return a == 16 && b == 20 ? 0 : 1;
}
