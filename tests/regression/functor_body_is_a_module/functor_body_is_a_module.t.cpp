#include <cassert>
#include <functor_body_is_a_module.h>
#include <iostream>

int main() {
  std::cout << FunctorBodyIsAModule::from_id << " "
            << FunctorBodyIsAModule::from_const << std::endl;
  assert(FunctorBodyIsAModule::from_id == 7);
  assert(FunctorBodyIsAModule::from_const == 3);
  return 0;
}
