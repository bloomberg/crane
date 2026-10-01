#include <endo_id_instance.h>

#include <cassert>
#include <iostream>

int main() {
  assert(EndoIdInstance::is_seven);
  std::cout << "endo_id_instance: ok" << std::endl;
  return 0;
}
