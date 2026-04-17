#include <dependent_elim_stdexcept_probe.h>

#include <iostream>

int main() {
  // This test reproduces a bug where dependent elimination over an indexed
  // type generates std::any and std::logic_error in unreachable branches
  // without including <any> or <stdexcept>.
  //
  // If this compiles and runs, the bug is fixed.
  auto s = DependentElimStdexceptProbe::sample;
  (void)s;
  std::cout << "dependent_elim_stdexcept_probe: passed" << std::endl;

  return 0;
}
