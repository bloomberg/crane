#include <local_fix_higher_order_probe.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) Nat LocalFixHigherOrderProbe::sample(const Nat &n) {
  return _sample_go<Nat>([](Nat x) { return x; }, n);
}
