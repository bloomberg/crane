#include <reuse_mixed_fields.h>

#include <cassert>

int main() {
  // test1: swap AsNat 10 20 -> AsPair 20 10 -> match AsPair -> a = 20
  assert(ReuseMixedFields::test1 == 20u);
  // test2: double swap = identity -> AsNat 5 6 -> 5*10+6 = 56
  assert(ReuseMixedFields::test2 == 56u);
  return 0;
}
