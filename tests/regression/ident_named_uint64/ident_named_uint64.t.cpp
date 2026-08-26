#include <ident_named_uint64.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = IdentNamedUint64::go;
  std::cout << "go = " << r << " (want 3)" << std::endl;
  assert(r == 3);
  return 0;
}
