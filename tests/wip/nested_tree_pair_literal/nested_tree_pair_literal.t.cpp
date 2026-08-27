// WIP: this test does not build yet.
//
// A non-uniform (nested) inductive `tree A := Lf : A -> tree A | Nd : tree (A * A) -> tree A`
// builds a literal value: the erased-parameter constructor still expects
// `uint64_t` where a `std::pair<uint64_t, uint64_t>` is supplied.
#include "nested_tree_pair_literal.h"

#include <cassert>
#include <iostream>

int main() {
  assert(NestedTreePairLiteral::go == 4);
  std::cout << "nested_tree_pair_literal: go = " << NestedTreePairLiteral::go << " PASSED" << std::endl;
  return 0;
}
