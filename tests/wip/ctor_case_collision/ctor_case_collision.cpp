#include "ctor_case_collision.h"

Nat CtorCaseCollision::get(const CtorCaseCollision::c &x) {
  if (std::holds_alternative<typename CtorCaseCollision::c::Foo>(x.v())) {
    const auto &[a0] = std::get<typename CtorCaseCollision::c::Foo>(x.v());
    return a0;
  } else {
    return Nat::o();
  }
}
