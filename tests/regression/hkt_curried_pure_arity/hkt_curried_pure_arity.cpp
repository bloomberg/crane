#include "hkt_curried_pure_arity.h"

std::optional<Nat> HktCurriedPureArity::run(const std::optional<Nat> &a,
                                            const std::optional<Nat> &b) {
  return ap<HktCurriedPureArity::ApOpt, Nat, Nat>(
      ap<HktCurriedPureArity::ApOpt, Nat, crane::fn<Nat(Nat)>>(
          pure<HktCurriedPureArity::ApOpt, crane::fn<crane::fn<Nat(Nat)>(Nat)>>(
              [](Nat x) { return [=](Nat) { return x; }; }),
          a),
      b);
}
