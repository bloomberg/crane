#include <dependent_vector_nth.h>
#include <iostream>
int main() {
  std::cout << DependentVectorNth::run << std::endl;
  return DependentVectorNth::run == 8 ? 0 : 1;
}
