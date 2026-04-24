#include <record_use_after_move.h>

#include <cassert>
#include <iostream>

int main() {
  using RUAM = RecordUseAfterMove;

  // double_let: payload of same record read twice.
  // Expected: 41 + 41 = 82
  auto r1 = RUAM::double_let;
  std::cout << "double_let = " << r1 << std::endl;
  assert(r1 == 82u);

  // two_consumers: same record passed to use_box twice.
  // Expected: 41 + 41 = 82
  auto r2 = RUAM::two_consumers;
  std::cout << "two_consumers = " << r2 << std::endl;
  assert(r2 == 82u);

  // problematic: same record moved into clone_box twice, then
  // used again in keep_box and a direct field access.
  // BUG: use-after-move on the shared_ptr wrapping the record.
  // Expected: payload = 41
  auto r3 = RUAM::problematic;
  std::cout << "problematic.payload = " << r3.payload << std::endl;
  assert(r3.payload == 41u);
  assert(r3.enabled == true);

  std::cout << "All record_use_after_move tests passed!" << std::endl;
  return 0;
}
