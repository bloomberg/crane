#include "function_return_branch_probe.h"

Nat FunctionReturnBranchProbe::make_adder(const Nat &n, const Nat &_x0) {
  return [=]() mutable -> std::function<Nat(Nat)> {
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      return [](Nat x) { return x; };
    } else {
      const auto &[a0] = std::get<typename Nat::S>(n.v());
      const Nat &a0_value = *a0;
      std::function<Nat(Nat)> f = [=](Nat _x0) mutable -> Nat {
        return make_adder(a0_value, _x0);
      };
      return [=](const Nat &x) mutable { return Nat::s(f(x)); };
    }
  }()(_x0);
}
