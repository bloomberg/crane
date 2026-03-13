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
  return Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))));
}

__attribute__((pure)) std::shared_ptr<Nat> TodoMonadicGlobalAlias::alias() {
  return base();
}

__attribute__((pure)) std::shared_ptr<Nat> TodoMonadicGlobalAlias::rebound() {
  std::shared_ptr<Nat> x = base();
  return Nat::ctor::S_(x);
}
