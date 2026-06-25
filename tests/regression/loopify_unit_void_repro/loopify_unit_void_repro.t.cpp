#include <loopify_unit_void_repro.h>

#include <iostream>

int main() {
  // This test reproduces a bug where Set Crane Loopify generates
  // `return std::monostate{}` inside a void lambda for sequenced
  // unit branches, causing a compilation error:
  //   error: void block should not return a value
  //
  // If this compiles and runs, the bug is fixed.
  auto r = LoopifyUnitVoidRepro::run();
  std::cout << "loopify_unit_void_repro: main returned" << std::endl;

  return 0;
}
