#include <typed_fit_alias_over_applied.h>

#include <cassert>
#include <iostream>

int main() {
  assert(TypedFitAliasOverApplied::run);
  assert(TypedFitAliasOverApplied::counter == 7);
  std::cout << "ok" << std::endl;
  return 0;
}
