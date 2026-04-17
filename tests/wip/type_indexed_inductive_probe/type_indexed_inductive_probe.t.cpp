#include <type_indexed_inductive_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // WIP: matching a type-indexed inductive at a concrete index should
  // recover the erased std::any payload via std::any_cast<Bool0>.
  // Currently fails to compile: the generated match returns d_a (std::any)
  // directly as Bool0 without a cast.
  auto s = TypeIndexedInductiveProbe::sample;
  std::cout << "sample = " << (s == Bool0::e_TRUE0 ? "true" : "false")
            << std::endl;
  assert(s == Bool0::e_TRUE0);

  return 0;
}
