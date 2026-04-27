#include <local_fix_higher_order_probe.h>

__attribute__((pure)) Nat LocalFixHigherOrderProbe::sample(const Nat &n) {
  return _sample_go<Nat>([](Nat x) { return x; }, n);
}
