#include <todo_monadic_global_alias.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

Nat TodoMonadicGlobalAlias::base() {
  return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
}

Nat TodoMonadicGlobalAlias::alias() { return base(); }

Nat TodoMonadicGlobalAlias::rebound() {
  Nat x = base();
  return Nat::s(x);
}
