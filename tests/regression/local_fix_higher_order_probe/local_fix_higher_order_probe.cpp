#include <local_fix_higher_order_probe.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Nat>
LocalFixHigherOrderProbe::sample(const std::shared_ptr<Nat> &n) {
  return _sample_go<std::shared_ptr<Nat>>(
      [](std::shared_ptr<Nat> x) { return x; }, n);
}
