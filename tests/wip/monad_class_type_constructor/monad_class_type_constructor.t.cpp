// WIP: this test does not build yet.
//
// A monad typeclass over a type constructor (`Mon (M : Type -> Type)`) emits
// the instance name in value position (`MOpt` used as a value), and the bind
// body applies a `std::any`.
#include "monad_class_type_constructor.h"

#include <cassert>
#include <iostream>

int main() {
  assert(MonadClassTypeConstructor::go == 42);
  std::cout << "monad_class_type_constructor: go = " << MonadClassTypeConstructor::go << " PASSED" << std::endl;
  return 0;
}
