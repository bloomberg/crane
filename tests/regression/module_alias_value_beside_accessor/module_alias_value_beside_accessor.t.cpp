#include <cassert>
#include <iostream>
#include <module_alias_value_beside_accessor.h>

int main() {
  std::cout << ModuleAliasValueBesideAccessor::from_alias << " "
            << ModuleAliasValueBesideAccessor::from_accessor << std::endl;
  assert(ModuleAliasValueBesideAccessor::from_alias == 1);
  assert(ModuleAliasValueBesideAccessor::from_accessor == 1);
  return 0;
}
