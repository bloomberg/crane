#include "reuse_token_in_closure.h"
#include <cassert>

int main() {
  using M = ReuseTokenInClosure;
  assert(M::suml(M::g(M::upto(UINT64_C(3)))) == 14);
  assert(M::suml(M::h(M::upto(UINT64_C(3)))) == 12);
  assert(M::suml(M::h(M::upto(UINT64_C(1000)))) == 1001000);
  return 0;
}
