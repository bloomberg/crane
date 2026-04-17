#include <dependent_return_unit_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where a definition with a dependent return
  // type (if b then unit else bool) extracts dep() as returning std::any,
  // but call sites use the concrete type without std::any_cast.
  //
  // If this compiles and runs, the bug is fixed.
  auto b = DependentReturnUnitProbe::sample_bool;
  std::cout << "sample_bool = " << static_cast<int>(b) << std::endl;
  assert(b == Bool0::e_FALSE0);

  return 0;
}
