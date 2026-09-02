#include <cassert>
#include <ctor_case_collision.h>

int main() {
  // `Foo` and `foo` differ only in case; both are reachable.
  assert(std::holds_alternative<typename CtorCaseCollision::c::Foo>(
      CtorCaseCollision::c::foo(Nat::s(Nat::o())).v()));
  assert(std::holds_alternative<typename CtorCaseCollision::c::Foo0>(
      CtorCaseCollision::c::foo0(true).v()));
  assert(std::holds_alternative<typename Nat::S>(
      CtorCaseCollision::get(CtorCaseCollision::c::foo(Nat::s(Nat::o()))).v()));
  assert(std::holds_alternative<typename Nat::O>(
      CtorCaseCollision::get(CtorCaseCollision::c::foo0(true)).v()));
  return 0;
}
