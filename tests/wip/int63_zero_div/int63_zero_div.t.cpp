#include <int63_zero_div.h>
#include <cassert>
#include <iostream>

int main() {
  // Rocq: 7 / 0 = 0, 7 mod 0 = 7, 1 << 70 = 0.
  std::cout << Int63ZeroDiv::d << " " << Int63ZeroDiv::m << " "
            << Int63ZeroDiv::s << std::endl;
  assert(Int63ZeroDiv::d == 0);
  assert(Int63ZeroDiv::m == 7);
  assert(Int63ZeroDiv::s == 0);
  return 0;
}
