// WIP: this test does not build yet.
//
// A constructor field holding the inductive under a pair
// (`N : (nat * c) -> c`) is stored as `shared_ptr<pair<uint64_t, c>>` but the
// generated code reads `.second` off the pointer.
#include "recursive_under_pair.h"

#include <cassert>
#include <iostream>

int main() {
  assert(RecursiveUnderPair::go == 1000);
  std::cout << "recursive_under_pair: go = " << RecursiveUnderPair::go << " PASSED" << std::endl;
  return 0;
}
