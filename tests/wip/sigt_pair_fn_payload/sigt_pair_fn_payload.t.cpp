// WIP: this test does not build yet.
//
// A `sigT` whose payload is a pair of a value and a function emits two
// contradictory `any_cast`s of the same pair, and the function result is left
// as `std::any` in a `uint64_t`-returning position.
#include "sigt_pair_fn_payload.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigtPairFnPayload::go == 4);
  std::cout << "sigt_pair_fn_payload: go = " << SigtPairFnPayload::go << " PASSED" << std::endl;
  return 0;
}
