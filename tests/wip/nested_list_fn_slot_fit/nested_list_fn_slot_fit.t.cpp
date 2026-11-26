#include <nested_list_fn_slot_fit.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << NestedListFnSlotFit::result << std::endl;
  assert(NestedListFnSlotFit::result == 13);
  return 0;
}
