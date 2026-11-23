#include <deque_fold_fix_init.h>

#include <iostream>

int main() {
  auto a = DequeFoldFixInit::t_1;
  auto b = DequeFoldFixInit::t_2;
  std::cout << a << " " << b << std::endl;
  return (a == 116 && b == 1) ? 0 : 1;
}
