#include <todo_monadic_global_alias.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) std::shared_ptr<Nat> TodoMonadicGlobalAlias::base() {
  return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
}

__attribute__((pure)) std::shared_ptr<Nat> TodoMonadicGlobalAlias::alias() {
  return base();
}

__attribute__((pure)) std::shared_ptr<Nat> TodoMonadicGlobalAlias::rebound() {
  std::shared_ptr<Nat> x = base();
  return Nat::s(x);
}
