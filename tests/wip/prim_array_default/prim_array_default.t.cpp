#include <prim_array_default.h>

#include <iostream>

int main() {
  auto d = PrimArrayDefault::dflt;
  std::cout << d << std::endl;
  return d == 7 ? 0 : 1;
}
