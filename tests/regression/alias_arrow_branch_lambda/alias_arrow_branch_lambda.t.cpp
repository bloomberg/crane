#include <alias_arrow_branch_lambda.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = AliasArrowBranchLambda::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 10);
  return 0;
}
