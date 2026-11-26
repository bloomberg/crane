#include <local_fix_partial_nth_slot.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << LocalFixPartialNthSlot::result << std::endl;
  assert(LocalFixPartialNthSlot::result == 3);
  return 0;
}
