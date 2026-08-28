// A typeclass parameterised by a type constructor (`Container (F : Type -> Type)`):
// the higher-kinded parameter becomes a promoted associated type holding the
// element-erased carrier.
#include "class_type_constructor_param.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ClassTypeConstructorParam::go == 5);
  std::cout << "class_type_constructor_param: go = " << ClassTypeConstructorParam::go << " PASSED" << std::endl;
  return 0;
}
