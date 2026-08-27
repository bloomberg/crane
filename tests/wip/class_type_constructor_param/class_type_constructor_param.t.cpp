// WIP: this test does not build yet.
//
// A typeclass parameterised by a type constructor (`Container (F : Type -> Type)`)
// collapses every method to `std::any` and generates a one-type-argument
// concept, so the static assertion fails and the method calls do not resolve.
#include "class_type_constructor_param.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ClassTypeConstructorParam::go == 5);
  std::cout << "class_type_constructor_param: go = " << ClassTypeConstructorParam::go << " PASSED" << std::endl;
  return 0;
}
