#include <typeclass_function_field_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where a typeclass instance whose field is
  // initialized with a stdlib function (negb) generates invalid C++:
  //   return a0->negb();
  // where a0 is a bool, which is not a pointer type.
  //
  // If this compiles and runs, the bug is fixed.
  auto r = TypeclassFunctionFieldProbe::sample;
  std::cout << "sample = " << r << std::endl;
  assert(r == false);

  return 0;
}
