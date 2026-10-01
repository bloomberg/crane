#include <ctor_family_index_any.h>

#include <cassert>
#include <iostream>

int main() {
  assert(CtorFamilyIndexAny::is_three);
  std::cout << "ctor_family_index_any: ok" << std::endl;
  return 0;
}
