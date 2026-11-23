#include <bake_bde.h>

#include <iostream>

int main() {
  auto a = BakeBde::total;
  auto b = BakeBde::pair_sum;
  std::cout << a << " " << b << std::endl;
  return (a == 6 && b == 6) ? 0 : 1;
}
