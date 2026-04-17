#include <record_function_field_stdlib_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where a record whose function field is
  // initialized with a stdlib function (negb) generates invalid C++:
  //   this->negb()
  // inside a static initializer, where `this` refers to a struct being
  // initialized, not an object with a negb method.
  //
  // If this compiles and runs, the bug is fixed.
  auto r = RecordFunctionFieldStdlibProbe::sample;
  std::cout << "sample = " << r << std::endl;
  assert(r == false);

  return 0;
}
