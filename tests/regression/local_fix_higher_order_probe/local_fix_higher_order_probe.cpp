#include <local_fix_higher_order_probe.h>

Nat LocalFixHigherOrderProbe::sample(const Nat &n) {
  return _sample_go<Nat>([](Nat x) { return x; }, n);
}
