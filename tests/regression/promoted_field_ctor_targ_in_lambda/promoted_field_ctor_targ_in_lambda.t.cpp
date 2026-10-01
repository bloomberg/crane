#include <promoted_field_ctor_targ_in_lambda.h>

#include <cassert>
#include <iostream>

int main() {
  assert(PromotedFieldCtorTargInLambda::is_zero);
  std::cout << "promoted_field_ctor_targ_in_lambda: ok" << std::endl;
  return 0;
}
