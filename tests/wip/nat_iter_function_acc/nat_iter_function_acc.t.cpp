#include <nat_iter_function_acc.h>
#include <iostream>
int main() {
  std::cout << NatIterFunctionAcc::run << std::endl;
  return NatIterFunctionAcc::run == 10 ? 0 : 1;
}
