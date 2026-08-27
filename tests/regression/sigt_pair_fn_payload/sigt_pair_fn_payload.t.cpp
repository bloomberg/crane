// A `sigT` whose payload is a pair of a value and a function: both pair
// components are boxed at the producer, so the consumer recovers the pair
// with a single any_cast and applies the callable.
#include "sigt_pair_fn_payload.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigtPairFnPayload::go == 4);
  std::cout << "sigt_pair_fn_payload: go = " << SigtPairFnPayload::go << " PASSED" << std::endl;
  return 0;
}
