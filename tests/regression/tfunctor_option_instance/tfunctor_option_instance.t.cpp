#include <tfunctor_option_instance.h>

#include <cassert>
#include <iostream>

int main() {
  assert(TfunctorOptionInstance::is_three);
  std::cout << "tfunctor_option_instance: ok" << std::endl;
  return 0;
}
