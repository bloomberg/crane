#include <pair_mix_bde.h>

#include <iostream>

int main() {
  auto a = PairMixBde::result;
  std::cout << a << std::endl;
  return a == 4 ? 0 : 1;
}
