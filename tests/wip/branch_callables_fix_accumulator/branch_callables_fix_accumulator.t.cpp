#include <branch_callables_fix_accumulator.h>

#include <iostream>

int main() {
  auto a = BranchCallablesFixAccumulator::t_1;
  std::cout << a << std::endl;
  return a == 0 ? 0 : 1;
}
