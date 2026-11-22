#include <self_comparison_global_werror.h>

#include <iostream>

int main() {
  auto a = SelfComparisonGlobalWerror::result;
  std::cout << a << std::endl;
  return a == 2 ? 0 : 1;
}
