#include <id_any_cast_flat_fn.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << IdAnyCastFlatFn::result << std::endl;
  assert(IdAnyCastFlatFn::result == 2);
  return 0;
}
