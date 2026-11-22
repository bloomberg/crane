#include <tmc_optional_bde.h>

#include <iostream>

int main() {
  auto a = TmcOptionalBde::total;
  std::cout << a << std::endl;
  return a == 6 ? 0 : 1;
}
