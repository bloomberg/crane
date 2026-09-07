#include <halist_dependent_value.h>
#include <iostream>
int main() {
  std::cout << HalistDependentValue::run << std::endl;
  return HalistDependentValue::run == 10 ? 0 : 1;
}
