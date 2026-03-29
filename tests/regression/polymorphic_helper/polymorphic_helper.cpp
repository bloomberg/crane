#include <polymorphic_helper.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Nat> foo(std::shared_ptr<Nat> n, const bool b) {
  return _foo_aux(std::move(n), n)->add(_foo_aux(b, n));
}
