#include <tmc_nested_ctor_wrap.h>
#include <cassert>

int main() {
  Nat n = TmcNestedCtorWrap::rsize(TmcNestedCtorWrap::spine(Nat::s(Nat::s(Nat::o()))));
  assert(std::holds_alternative<typename Nat::S>(n.v()));
  return 0;
}
