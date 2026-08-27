// A non-uniform (nested) inductive
// ([tree A := Lf : A -> tree A | Nd : tree (A * A) -> tree A]) has its type
// parameter erased, so a literal value built at [tree nat] passes a
// [std::pair] through the erased constructor.
#include "nested_tree_pair_literal.h"

#include <cassert>
#include <iostream>

int main() {
  assert(NestedTreePairLiteral::go == 4);
  std::cout << "nested_tree_pair_literal: go = " << NestedTreePairLiteral::go << " PASSED" << std::endl;
  return 0;
}
