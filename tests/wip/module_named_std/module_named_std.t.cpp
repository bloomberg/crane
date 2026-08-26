#include <module_named_std.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = ModuleNamedStd::go;
  std::cout << "go = " << r << " (want 1)" << std::endl;
  assert(r == 1);
  return 0;
}
