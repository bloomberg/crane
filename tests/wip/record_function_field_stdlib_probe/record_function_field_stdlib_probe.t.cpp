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
  // negb(true) = false
  std::cout << "sample = " << (r == Bool0::e_FALSE0 ? "false" : "true") << std::endl;
  assert(r == Bool0::e_FALSE0);

  return 0;
}
