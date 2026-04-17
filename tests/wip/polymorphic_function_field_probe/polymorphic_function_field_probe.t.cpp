#include <polymorphic_function_field_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where a polymorphic record field
  //   apply : forall A : Type, A -> A
  // is extracted as std::function<std::any(std::any)>, but the generated
  // call site passes two arguments (an erased type placeholder + the value),
  // causing a compile error:
  //   no matching function for call to std::function<std::any(std::any)>
  //   (requires 1 argument, but 2 were provided)
  //
  // If this compiles and runs, the bug is fixed.
  auto r = PolymorphicFunctionFieldProbe::sample_bool;
  // apply is the identity, so apply p bool true = true
  std::cout << "sample_bool = " << (r == Bool0::e_TRUE0 ? "true" : "false") << std::endl;
  assert(r == Bool0::e_TRUE0);

  return 0;
}
