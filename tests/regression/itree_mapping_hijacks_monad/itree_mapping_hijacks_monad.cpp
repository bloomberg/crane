#include "itree_mapping_hijacks_monad.h"

Err<Nat> twice(const Err<Nat> &x) {
  return Monad_Err::template bind<Nat, Nat>(x, [=](const Nat &a) {
    return Monad_Err::template bind<Nat, Nat>(
        x, [=](Nat b) { return Monad_Err::template ret<Nat>(a.add(b)); });
  });
}

Err<Nat> ItreeMappingHijacksMonad::use(const Nat &n) {
  return twice(Err<Nat>::ok(n));
}
