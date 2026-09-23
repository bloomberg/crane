#include "function_return_branch_probe.h"

/// A recursive function whose match branches return different lambda
/// expressions.  Crane generates an inner lambda with no explicit return type,
/// causing C++ to fail to deduce a common return type across the two distinct
/// closure types.
Nat FunctionReturnBranchProbe::make_adder(const Nat &n, const Nat &x0_) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return x0_;
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    std::function<Nat(Nat)> f = [&](Nat _x0) -> Nat {
      return make_adder(*a0, _x0);
    };
    return Nat::s(f(x0_));
  }
}
