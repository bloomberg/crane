#include "let_shadows_match_binder.h"

Nat LetShadowsMatchBinder::two(const std::optional<Nat> &o) {
  Nat x;
  if (o.has_value()) {
    const Nat &x0 = *o;
    x = x0;
  } else {
    x = Nat::s(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
  }
  return Nat::s(std::move(x));
}

Nat LetShadowsMatchBinder::three(const std::optional<Nat> &x) {
  Nat x0;
  if (x.has_value()) {
    const Nat &x1 = *x;
    x0 = x1;
  } else {
    x0 = Nat::s(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
  }
  return Nat::s(std::move(x0));
}
