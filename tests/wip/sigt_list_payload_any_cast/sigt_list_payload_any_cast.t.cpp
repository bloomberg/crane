// WIP: this test does not build yet.
//
// A `sigT` payload holding a `list nat` is stored as `List<uint64_t>` by the
// producer but read back through a doubled `any_cast<List<std::any>>` at the
// consumer, which throws `std::bad_any_cast` at run time.
#include "sigt_list_payload_any_cast.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigtListPayloadAnyCast::go == 3);
  std::cout << "sigt_list_payload_any_cast: go = " << SigtListPayloadAnyCast::go << " PASSED" << std::endl;
  return 0;
}
