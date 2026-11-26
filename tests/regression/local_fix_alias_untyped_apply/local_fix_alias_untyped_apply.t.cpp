#include <local_fix_alias_untyped_apply.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << LocalFixAliasUntypedApply::result << std::endl;
  assert(LocalFixAliasUntypedApply::result == 703);
  return 0;
}
