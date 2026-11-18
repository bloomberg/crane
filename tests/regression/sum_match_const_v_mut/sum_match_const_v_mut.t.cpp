// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <sum_match_const_v_mut.h>

#include <iostream>

int main() {
  if (SumMatchConstVMut::t_1 != 10) {
    std::cout << "FAIL: t_1" << std::endl;
    return 1;
  }
  if (SumMatchConstVMut::t_2 != 68) {
    std::cout << "FAIL: t_2" << std::endl;
    return 1;
  }
  if (SumMatchConstVMut::t_3 != 41) {
    std::cout << "FAIL: t_3" << std::endl;
    return 1;
  }
  std::cout << "All sum_match_const_v_mut tests passed!" << std::endl;
  return 0;
}
