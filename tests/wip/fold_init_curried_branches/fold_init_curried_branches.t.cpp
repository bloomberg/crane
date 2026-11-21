#include <fold_init_curried_branches.h>

#include <iostream>

int main() {
  auto a = FoldInitCurriedBranches::t_1;
  std::cout << a << std::endl;
  return a == 12 ? 0 : 1;
}
