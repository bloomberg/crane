#include <function_return_branch_probe.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A recursive function whose match branches return different lambda
/// expressions.  Crane generates an inner lambda with no explicit return type,
/// causing C++ to fail to deduce a common return type across the two distinct
/// closure types.
std::shared_ptr<Nat>
FunctionReturnBranchProbe::make_adder(const std::shared_ptr<Nat> &n,
                                      const std::shared_ptr<Nat> &_x0) {
  return [&]() {
    if (std::holds_alternative<typename Nat::O>(n->v())) {
      return [](std::shared_ptr<Nat> x) { return x; };
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(n->v());
      std::function<std::shared_ptr<Nat>(std::shared_ptr<Nat>)> f =
          [=](const std::shared_ptr<Nat> &_x0) mutable -> std::shared_ptr<Nat> {
        return make_adder(d_a0, _x0);
      };
      return
          [=](const std::shared_ptr<Nat> &x) mutable { return Nat::s(f(x)); };
    }
  }()(_x0);
}
