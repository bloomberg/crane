#include <class_superclass_explicit.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = ClassSuperclassExplicit::go;
  std::cout << "go = " << r << " (want 7)" << std::endl;
  assert(r == 7);
  return 0;
}
