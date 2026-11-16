#include "module_type_name_collision.h"

Opt<Nat> double0(Nat n) { return opt_monad::template ret<Nat>(n.add(n)); }

Opt<Nat> ModuleTypeNameCollision::use(Nat n) {
  return opt_monad::template bind<Nat, Nat>(
      double0(std::move(n)),
      [](const Nat &x) { return opt_monad::template ret<Nat>(Nat::s(x)); });
}
