#include <todo_monadic_global_alias.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Nat> TodoMonadicGlobalAlias::base() {
  return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
}

std::shared_ptr<Nat> TodoMonadicGlobalAlias::alias() { return base(); }

std::shared_ptr<Nat> TodoMonadicGlobalAlias::rebound() {
  std::shared_ptr<Nat> x = base();
  return Nat::s(x);
}
