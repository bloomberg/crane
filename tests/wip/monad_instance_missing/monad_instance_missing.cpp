#include "monad_instance_missing.h"

EOU<Nat> double0(const Nat &n) {
  return Monad0::template ret<EOU_monad, Nat>(n.add(n));
}

EOU<Nat> MonadInstanceMissing::use(const Nat &n) {
  return Monad0::template bind<MonadInstanceMissing::EOU_monad, Nat, Nat>(
      double0(n), [](Nat x) {
        return Monad0::template ret<MonadInstanceMissing::EOU_monad, Nat>(
            Nat::s(x));
      });
}
