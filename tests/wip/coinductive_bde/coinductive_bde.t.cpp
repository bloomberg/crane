#include <coinductive_bde.h>

#include <iostream>

int main() {
  auto a = CoinductiveBde::total;
  std::cout << a << std::endl;
  return a == 18 ? 0 : 1;
}
