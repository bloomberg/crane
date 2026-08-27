// A `sigT` payload holding a `list nat` round-trips through the field's
// erased `std::any`: producer and consumer must agree on the element-erased
// representation.
#include "sigt_list_payload_any_cast.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigtListPayloadAnyCast::go == 3);
  std::cout << "sigt_list_payload_any_cast: go = " << SigtListPayloadAnyCast::go << " PASSED" << std::endl;
  return 0;
}
