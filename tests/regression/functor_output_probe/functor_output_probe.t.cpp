#include <functor_output_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where functor/module type extraction
  // generates std::convertible_to and std::same_as concepts without
  // including <concepts>.
  //
  // If this compiles and runs, the bug is fixed.
  auto r = FunctorOutputProbe::sample;
  std::cout << "sample = " << r << std::endl;
  assert(r == 0u);

  return 0;
}
