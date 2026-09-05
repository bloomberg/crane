#include <nat_literal_overflow.h>
#include <cassert>
#include <iostream>
int main() {
  // The out-of-range assertions run while NatLiteralOverflow.vo is built: the
  // Fail commands reject literals that uint64_t cannot hold. Here we only
  // check that the largest one it can hold survives extraction exactly.
  std::cout << NatLiteralOverflow::max64 << " " << NatLiteralOverflow::total
            << "\n";
  assert(NatLiteralOverflow::max64 == UINT64_MAX);
  assert(NatLiteralOverflow::total == 10u);
  return 0;
}
