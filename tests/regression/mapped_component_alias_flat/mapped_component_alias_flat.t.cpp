#include <mapped_component_alias_flat.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << MappedComponentAliasFlat::result << std::endl;
  assert(MappedComponentAliasFlat::result == 4);
  return 0;
}
