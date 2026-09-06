#include <cps_continuation_copy.h>
#include <iostream>
int main() {
  std::cout << CpsContinuationCopy::run << std::endl;
  return CpsContinuationCopy::run == 4999950000ULL ? 0 : 1;
}
