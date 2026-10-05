#include "local_fix_higher_order_probe.h"

Nat LocalFixHigherOrderProbe::sample(const Nat &n) {
  auto go = [](crane::fn<Nat(Nat)> k, const Nat &n0) -> Nat {
    Nat _loop_n0 = n0;
    crane::fn<Nat(Nat)> _loop_k = std::move(k);
    while (true) {
      if (std::holds_alternative<typename Nat::O>(_loop_n0.v())) {
        return _loop_k(Nat::o());
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_loop_n0.v());
        const Nat &a0_value = *a0;
        _loop_n0 = a0_value;
        _loop_k = [=](const Nat &x) { return _loop_k(Nat::s(x)); };
      }
    }
  };
  return go([](Nat x) { return x; }, n);
}
