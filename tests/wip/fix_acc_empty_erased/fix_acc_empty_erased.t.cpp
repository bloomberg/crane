#include <fix_acc_empty_erased.h>

#include <iostream>

int main() {
  auto a = FixAccEmptyErased::t_opt;
  auto b = FixAccEmptyErased::t_deque;
  std::cout << a << " " << b << std::endl;
  return (a == 0 && b == 0) ? 0 : 1;
}
