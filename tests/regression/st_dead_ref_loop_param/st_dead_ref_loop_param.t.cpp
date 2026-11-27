#include <st_dead_ref_loop_param.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << STDeadRefLoopParam::result << std::endl;
  assert(STDeadRefLoopParam::result == 53);
  return 0;
}
