#include <deque_fold_fix_init.h>

#include <iostream>

int main() {
  auto a = DequeFoldFixInit::t_1;
  std::cout << a << std::endl;
  return a == 116 ? 0 : 1;
}
