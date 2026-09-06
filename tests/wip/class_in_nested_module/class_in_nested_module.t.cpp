#include <class_in_nested_module.h>
#include <iostream>
int main() {
  std::cout << ClassInNestedModule::run << std::endl;
  return ClassInNestedModule::run == 6 ? 0 : 1;
}
