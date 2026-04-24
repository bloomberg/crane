#include <sigt_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // Regression: existT with a type-valued witness (x : A where A : Type)
  // previously leaked the concrete type into the second SigT template param,
  // producing SigT<std::any, Bool0> vs. the declared SigT<std::any, std::any>.
  // The fix erases subsequent params when a leading param is MLdummy Ktype.
  auto result = SigTProbe::sample;
  // sample = match packed with existT _ _ _ => 0 end = 0
  std::cout << "sample = "
            << (std::holds_alternative<Nat::O>(result.v()) ? "0" : "other")
            << std::endl;
  assert(std::holds_alternative<Nat::O>(result.v()));

  return 0;
}
