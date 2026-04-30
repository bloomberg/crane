#include <polymorphic_helper.h>

Nat foo(Nat n, const bool &b) {
  return _foo_aux(std::move(n), n).add(_foo_aux(b, n));
}
