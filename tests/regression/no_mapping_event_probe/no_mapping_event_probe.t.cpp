#include <no_mapping_event_probe.h>

#include <iostream>

int main() {
  // This test reproduces a simpler variant of the void/monostate bug
  // using an inductive event type (without axioms or Set Crane Loopify).
  //
  // If this compiles and runs, the bug is fixed.
  std::cout << "no_mapping_event_probe: compiled successfully" << std::endl;

  return 0;
}
