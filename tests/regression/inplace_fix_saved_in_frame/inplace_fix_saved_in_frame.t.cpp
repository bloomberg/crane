#include <inplace_fix_saved_in_frame.h>

#include <cassert>
#include <iostream>

int main() {
  // insert_shift 1 [10; 20; 30] is four lists, each headed by 11 = 10 + 1:
  // the first built in the turn for 10, the other three by that turn's
  // map_k, which prepends its k.  A map_k reading a k that is no longer its
  // own (the slot a later turn reused) heads them otherwise.
  auto r = InplaceFixSavedInFrame::test;
  std::cout << "test = " << r << std::endl;
  assert(r == 44);
  return 0;
}
