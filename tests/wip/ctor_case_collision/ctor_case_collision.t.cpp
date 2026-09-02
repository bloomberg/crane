#include <ctor_case_collision.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::O>(
      CtorCaseCollision::get(CtorCaseCollision::c::foo(Bool0::TRUE_)).v()));
  return 0;
}
