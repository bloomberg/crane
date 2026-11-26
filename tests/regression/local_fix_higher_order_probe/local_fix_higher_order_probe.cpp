#include "local_fix_higher_order_probe.h"

Nat LocalFixHigherOrderProbe::sample(const Nat &n) {
  const crane::fn<Nat(Nat)> &_lc1_k = [](Nat x) { return x; };
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const Nat *_lc1_loop_n0 = &n;
  crane::fn<Nat(Nat)> _lc1_loop_k = _lc1_k;
  while (true) {
    if (std::holds_alternative<typename Nat::O>(_lc1_loop_n0->v())) {
      return _lc1_loop_k(Nat::o());
    } else {
      const auto &[a0] = std::get<typename Nat::S>(_lc1_loop_n0->v());
      const Nat &a0_value = *a0;
      _lc1_loop_n0 = &a0_value;
      _lc1_loop_k = [=](const Nat &x) { return _lc1_loop_k(Nat::s(x)); };
    }
  }
}
