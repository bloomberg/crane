#include <local_fix_higher_order_probe.h>

#include <cassert>
#include <iostream>

int nat_to_int(const std::shared_ptr<Nat> &n) {
  int count = 0;
  auto cur = n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    const auto &[pred] = std::get<Nat::S>(cur->v());
    cur = pred;
    ++count;
  }
  return count;
}

int main() {
  // This test reproduces a bug where a local recursive helper with a
  // higher-order accumulator generates a templated C++ function whose
  // recursive call changes the template argument on every iteration,
  // causing recursive template instantiation until the compiler hits
  // its depth limit.
  //
  // If this compiles and runs, the bug is fixed.
  auto result = LocalFixHigherOrderProbe::run;
  // sample 3 = go id 3 = go (fun x => S x) 2 = go (fun x => S (S x)) 1
  //          = go (fun x => S (S (S x))) 0 = (fun x => S (S (S x))) 0
  //          = S (S (S 0)) = 3
  assert(nat_to_int(result) == 3);

  return 0;
}
