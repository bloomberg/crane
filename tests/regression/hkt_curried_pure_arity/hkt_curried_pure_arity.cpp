#include "hkt_curried_pure_arity.h"

std::optional<Nat> HktCurriedPureArity::run(const std::optional<Nat> &a,
                                            const std::optional<Nat> &b) {
  return ap<HktCurriedPureArity::ApOpt, Nat, Nat>(
      ap<HktCurriedPureArity::ApOpt, Nat, std::function<Nat(Nat)>>(
          pure<HktCurriedPureArity::ApOpt,
               std::function<std::function<Nat(Nat)>(Nat)>>([](const auto &x) {
            return [=](const auto &) mutable { return x; };
          }),
          a),
      b);
}
