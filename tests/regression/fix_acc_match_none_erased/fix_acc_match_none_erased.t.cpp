#include <fix_acc_match_none_erased.h>

#include <iostream>

int main() {
  auto a = FixAccMatchNoneErased::result;
  std::cout << a << std::endl;
  return a == 2 ? 0 : 1;
}
