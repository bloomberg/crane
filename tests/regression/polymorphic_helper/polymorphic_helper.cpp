#include <polymorphic_helper.h>

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

std::shared_ptr<Nat> foo(std::shared_ptr<Nat> n, const bool b) {
  return _foo_aux(std::move(n), n)->add(_foo_aux(b, n));
}
