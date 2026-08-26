#include <class_superclass_field.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = ClassSuperclassField::go;
  std::cout << "go = " << r << " (want 1)" << std::endl;
  assert(r == 1);
  return 0;
}
