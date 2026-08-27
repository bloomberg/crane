// WIP: this test does not build yet.
//
// A typeclass method that is polymorphic in its own type argument
// (`forall A, (A -> A) -> A -> A`) erases the argument to
// `std::function<std::any(std::any)>`, but the instance body is emitted as a
// concrete lambda, so no viable conversion exists.
#include "class_poly_method_erased_fn.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ClassPolyMethodErasedFn::go == 7);
  std::cout << "class_poly_method_erased_fn: go = " << ClassPolyMethodErasedFn::go << " PASSED" << std::endl;
  return 0;
}
