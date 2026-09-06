#include <modtype_local_type_ref.h>
#include <cassert>
#include <iostream>

int main() {
  std::cout << ModtypeLocalTypeRef::run << std::endl;
  assert(ModtypeLocalTypeRef::run == 46);
  return 0;
}
