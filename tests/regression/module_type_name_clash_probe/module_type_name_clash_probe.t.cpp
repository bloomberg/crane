#include <module_type_name_clash_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where a module and an inductive type with
  // the same Rocq name in the same enclosing module emit two C++ structs
  // with the same name, causing a redefinition error.
  //
  // If this compiles and runs, the bug is fixed.
  auto result = ModuleTypeNameClashProbe::sample;
  assert(result == Bool0::e_TRUE0);

  return 0;
}
