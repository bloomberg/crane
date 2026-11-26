#include <sig_closure_witness_fit.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << SigClosureWitnessFit::result << std::endl;
  assert(SigClosureWitnessFit::result == 31);
  std::cout << "result2 = " << SigClosureWitnessFit::result2 << std::endl;
  assert(SigClosureWitnessFit::result2 == 5);
  return 0;
}
