// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <frame_binder_local_fix_acc.h>

#include <iostream>

int main() {
  if (FrameBinderLocalFixAcc::t_1 != 0) {
    std::cout << "FAIL: t_1" << std::endl;
    return 1;
  }
  std::cout << "All frame_binder_local_fix_acc tests passed!" << std::endl;
  return 0;
}
