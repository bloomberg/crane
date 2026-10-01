#include <sibling_module_qualified.h>

#include <cassert>
#include <iostream>

int main() {
  assert(SiblingModuleQualified::is_one);
  std::cout << "sibling_module_qualified: ok" << std::endl;
  return 0;
}
