#include <reuse_tag_mismatch.h>

#include <cassert>

int main() {
  // test1: flip GoUp 42, expected GoDown 42, so result = 2
  assert(ReuseTagMismatch::test1 == 2u);
  // test2: no flip, GoUp 42 stays, result = 1
  assert(ReuseTagMismatch::test2 == 1u);
  // test3: flip GoDown 100, expected GoUp 100, result = 3
  assert(ReuseTagMismatch::test3 == 3u);
  // test4: flip GoUp 10 -> GoDown 10, result = 10
  assert(ReuseTagMismatch::test4 == 10u);
  return 0;
}
