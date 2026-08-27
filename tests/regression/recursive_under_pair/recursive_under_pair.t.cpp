// A constructor field holding the inductive under a pair
// ([N : (nat * c) -> c]) is stored as [shared_ptr<pair<uint64_t, c>>].  The
// pattern match must dereference the pointer before projecting [.second].
#include "recursive_under_pair.h"

#include <cassert>
#include <iostream>

int main() {
  assert(RecursiveUnderPair::go == 1000);
  std::cout << "recursive_under_pair: go = " << RecursiveUnderPair::go << " PASSED" << std::endl;
  return 0;
}
