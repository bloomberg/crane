// A monad typeclass over a type constructor (`Mon (M : Type -> Type)`) with an
// `option`-based carrier, including an erased callback passed to `mbind`.
#include "monad_class_type_constructor.h"

#include <cassert>
#include <iostream>

int main() {
  assert(MonadClassTypeConstructor::go == 42);
  std::cout << "monad_class_type_constructor: go = " << MonadClassTypeConstructor::go << " PASSED" << std::endl;
  return 0;
}
