#include <fix_move_capture.h>

#include <cassert>

int main() {
  // test1: f([10, 20, 30])
  // Expected: 67 if correct, but f() should crash
  // because go's [&] capture references moved-from l
  assert(FixMoveCapture::test1 == 67u);

  // test2: f2([5, 15])
  // f2 forces evaluation order: go(3) computed before l is moved
  // Should pass: 23 + 3 = 26
  assert(FixMoveCapture::test2 == 26u);

  return 0;
}
