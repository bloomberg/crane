// WIP: this test does not build yet.
//
// Using `nth_error` on a `list (nat -> nat)` emits the erasure-converting
// `List` constructor with a doubled qualifier
// (`typename List::typename List::template list<_U>::Nil`), which is not even
// syntactically valid C++.
#include "list_erasure_ctor_typename.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ListErasureCtorTypename::go == 42);
  std::cout << "list_erasure_ctor_typename: go = " << ListErasureCtorTypename::go << " PASSED" << std::endl;
  return 0;
}
