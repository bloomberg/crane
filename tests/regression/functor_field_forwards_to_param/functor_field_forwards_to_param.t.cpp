#include <functor_field_forwards_to_param.h>

#include <cassert>

int main() {
  // Unbounded self-recursion here overflows the stack rather than failing an
  // assertion, so reaching the second line at all is most of the test.
  assert(FunctorFieldForwardsToParam::go(true, true));
  assert(!FunctorFieldForwardsToParam::go(true, false));
  assert(FunctorFieldForwardsToParam::go2(true, true));
  assert(!FunctorFieldForwardsToParam::go2(true, false));
  return 0;
}
