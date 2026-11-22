#include <alias_param_convention_check.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = AliasParamConventionCheck::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 4);
  return 0;
}
