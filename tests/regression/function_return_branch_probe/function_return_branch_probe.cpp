#include <function_return_branch_probe.h>

/// A recursive function whose match branches return different lambda
/// expressions.  Crane generates an inner lambda with no explicit return type,
/// causing C++ to fail to deduce a common return type across the two distinct
/// closure types.
Nat FunctionReturnBranchProbe::make_adder(const Nat &n, const Nat &_x0) {
  return [=]() mutable -> std::function<Nat(Nat)> {
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      return [](Nat x) { return x; };
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(n.v());
      Nat d_a0_value = Nat(*(d_a0));
      std::function<Nat(Nat)> f = [=](Nat _x0) mutable -> Nat {
        return make_adder(d_a0_value, _x0);
      };
      return [=](const Nat &x) mutable { return Nat::s(f(x)); };
    }
  }()(_x0);
}
