#include <tail_call_same_name_other_module.h>

#include <cassert>
#include <unistd.h>

// THE FAILURE HERE IS A HANG, NOT A COMPILE ERROR.
//
// Loopification used to read `T1::t1::cmp` -- called from `T2::t2::cmp`, and
// sharing nothing with it but a label -- as a self-call, park it, and discard
// the real callee, leaving a `while (true)` with no exit.  Perfectly valid
// C++.  The alarm is what turns that back into a test failure instead of a
// wedged suite.
int main() {
  alarm(20);
  // T2.cmp (C2 1) (C2 2) = T1.cmp (C1 1) (C1 2) = 1 + 2
  assert(TailCallSameNameOtherModule::ok);
  return 0;
}
