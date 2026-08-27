// Nested functor application: a field read through a functor's module
// parameter may be a static data member in one argument module and a nullary
// accessor in another; both spellings must work at the use site.
#include "functor_value_field_call.h"

#include <cassert>
#include <iostream>

int main() {
  assert(FunctorValueFieldCall::go == 0);
  std::cout << "functor_value_field_call: go = " << FunctorValueFieldCall::go << " PASSED" << std::endl;
  return 0;
}
