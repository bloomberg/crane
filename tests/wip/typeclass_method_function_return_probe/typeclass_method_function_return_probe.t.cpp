#include <typeclass_method_function_return_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where partial application of a typeclass
  // method generates curried calls (make(arg1)(arg2)) to an uncurried
  // static method (make(arg1, arg2)).
  //
  // If this compiles and runs, the bug is fixed.
  auto result = TypeclassMethodFunctionReturnProbe::sample;
  assert(result == Bool0::e_FALSE0);

  return 0;
}
