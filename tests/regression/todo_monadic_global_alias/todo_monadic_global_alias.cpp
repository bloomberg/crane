#include <todo_monadic_global_alias.h>

Nat TodoMonadicGlobalAlias::base() {
  return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
}

Nat TodoMonadicGlobalAlias::alias() { return base(); }

Nat TodoMonadicGlobalAlias::rebound() {
  Nat x = base();
  return Nat::s(x);
}
