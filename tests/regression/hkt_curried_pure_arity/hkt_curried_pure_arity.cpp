#include "hkt_curried_pure_arity.h"

std::optional<Nat> HktCurriedPureArity::run(const std::optional<Nat> &a,
                                            const std::optional<Nat> &b) {
  return HktCurriedPureArity::ApOpt::template ap<Nat, Nat>(
      HktCurriedPureArity::ApOpt::template ap<Nat, crane::fn<Nat(Nat)>>(
          HktCurriedPureArity::ApOpt::template pure<
              crane::fn<crane::fn<Nat(Nat)>(Nat)>>(
              [](Nat x) { return [=](Nat) { return x; }; }),
          a),
      b);
}
