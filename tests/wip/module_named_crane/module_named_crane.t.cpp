#include <module_named_crane.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = ModuleNamedCrane::go;
  std::cout << "go = " << r << " (want 2)" << std::endl;
  assert(r == 2);
  return 0;
}
