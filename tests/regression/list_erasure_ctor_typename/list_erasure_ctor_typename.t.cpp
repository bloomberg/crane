// Using `nth_error` on a `list (nat -> nat)` instantiates the
// erasure-converting `List` constructor; its body must spell the source
// instantiation's constructor structs as
// `typename List::template list<_U>::Nil`.
#include "list_erasure_ctor_typename.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ListErasureCtorTypename::go == 42);
  std::cout << "list_erasure_ctor_typename: go = " << ListErasureCtorTypename::go << " PASSED" << std::endl;
  return 0;
}
