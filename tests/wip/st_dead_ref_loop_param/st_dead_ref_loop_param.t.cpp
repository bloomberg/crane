#include <st_dead_ref_loop_param.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << StDeadRefLoopParam::result << std::endl;
  assert(StDeadRefLoopParam::result == 53);
  return 0;
}
