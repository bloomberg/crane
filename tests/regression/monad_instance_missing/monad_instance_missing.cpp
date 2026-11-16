#include "monad_instance_missing.h"

EOU<Nat> double0(Nat n) { return EOU_monad::template ret<Nat>(n.add(n)); }

EOU<Nat> MonadInstanceMissing::use(Nat n) {
  return EOU_monad::template bind<Nat, Nat>(
      double0(std::move(n)),
      [](const Nat &x) { return EOU_monad::template ret<Nat>(Nat::s(x)); });
}
