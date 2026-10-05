#include "module_type_name_collision.h"

Opt<Nat> double0(Nat n) {
  return Monad0::template ret<opt_monad, Nat>(n.add(n));
}

Opt<Nat> ModuleTypeNameCollision::use(Nat n) {
  return Monad0::template bind<opt_monad, Nat, Nat>(
      double0(std::move(n)), [](const Nat &x) {
        return Monad0::template ret<opt_monad, Nat>(Nat::s(x));
      });
}
