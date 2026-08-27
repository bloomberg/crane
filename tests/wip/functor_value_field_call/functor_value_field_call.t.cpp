// WIP: this test does not build yet.
//
// Nested functor application emits a call `C::zero()` for a module field that
// the argument module defines as a value (`static inline const uint64_t`), so
// the extracted header fails with "called object type 'uint64_t' is not a
// function or function pointer".
#include "functor_value_field_call.h"

#include <cassert>
#include <iostream>

int main() {
  assert(FunctorValueFieldCall::go == 0);
  std::cout << "functor_value_field_call: go = " << FunctorValueFieldCall::go << " PASSED" << std::endl;
  return 0;
}
