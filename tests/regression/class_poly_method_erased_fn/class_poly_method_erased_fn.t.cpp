// A typeclass method polymorphic in its own type argument
// (`forall A, (A -> A) -> A -> A`): the instance takes the erased
// `std::function<std::any(std::any)>`, so the projection must adapt the
// caller's concrete closure to it.
#include "class_poly_method_erased_fn.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ClassPolyMethodErasedFn::go == 7);
  std::cout << "class_poly_method_erased_fn: go = " << ClassPolyMethodErasedFn::go << " PASSED" << std::endl;
  return 0;
}
