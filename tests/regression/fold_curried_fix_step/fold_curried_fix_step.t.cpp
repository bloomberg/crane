#include <fold_curried_fix_step.h>

#include <iostream>

int main() {
  auto a = FoldCurriedFixStep::result;
  std::cout << a << std::endl;
  return a == 34 ? 0 : 1;
}
