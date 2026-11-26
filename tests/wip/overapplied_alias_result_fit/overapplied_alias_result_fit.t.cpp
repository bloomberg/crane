#include <overapplied_alias_result_fit.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << OverappliedAliasResultFit::result << std::endl;
  assert(OverappliedAliasResultFit::result == 705);
  return 0;
}
