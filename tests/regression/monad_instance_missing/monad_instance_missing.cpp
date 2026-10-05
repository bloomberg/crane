#include "monad_instance_missing.h"

EOU<Nat> double0(Nat n) {
  return Monad0::template ret<EOU_monad, Nat>(n.add(n));
}

EOU<Nat> MonadInstanceMissing::use(Nat n) {
  return Monad0::template bind<EOU_monad, Nat, Nat>(
      double0(std::move(n)), [](const Nat &x) {
        return Monad0::template ret<EOU_monad, Nat>(Nat::s(x));
      });
}
