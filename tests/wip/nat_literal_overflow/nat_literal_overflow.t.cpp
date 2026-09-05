#include <nat_literal_overflow.h>
#include <cassert>
#include <iostream>
int main() {
  std::cout << NatLiteralOverflow::big << " " << NatLiteralOverflow::total << " " << NatLiteralOverflow::wraps << "\n";
  assert(!NatLiteralOverflow::wraps);
  return 0;
}
