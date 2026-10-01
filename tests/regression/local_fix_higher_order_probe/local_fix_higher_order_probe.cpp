#include "local_fix_higher_order_probe.h"

Nat LocalFixHigherOrderProbe::sample(const Nat &n) {
  auto go_impl = [](auto &_self_go, crane::fn<Nat(Nat)> k,
                    const Nat &n0) -> Nat {
    if (std::holds_alternative<typename Nat::O>(n0.v())) {
      return k(Nat::o());
    } else {
      const auto &[a0] = std::get<typename Nat::S>(n0.v());
      const Nat &a0_value = *a0;
      return _self_go(
          _self_go, [=](const Nat &x) { return k(Nat::s(x)); }, a0_value);
    }
  };
  auto go = [&](crane::fn<Nat(Nat)> k, const Nat &n0) -> Nat {
    return go_impl(go_impl, k, n0);
  };
  return go([](Nat x) { return x; }, n);
}
