#include <typed_fit_known_class.h>

#include <cassert>
#include <iostream>

int main() {
  assert(TypedFitKnownClass::answered);
  assert(TypedFitKnownClass::measure_three == 3);
  std::cout << "ok" << std::endl;
  return 0;
}
