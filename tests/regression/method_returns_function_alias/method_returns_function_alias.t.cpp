#include <cassert>
#include <method_returns_function_alias.h>

int main() {
  using M = MethodReturnsFunctionAlias;
  assert(M::t1);
  assert(M::t2);
  assert(M::t3);
  assert(!M::t4);
  return 0;
}
