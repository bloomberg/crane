#include "module_type_name_collision.h"

Opt<Nat> double0(const Nat &n) {
  return Monad0::template ret<opt_monad, Nat>(n.add(n));
}

Opt<Nat> ModuleTypeNameCollision::use(const Nat &n) {
  return Monad0::template bind<opt_monad, Nat, Nat>(double0(n), [](Nat x) {
    return Monad0::template ret<opt_monad, Nat>(Nat::s(x));
  });
}
