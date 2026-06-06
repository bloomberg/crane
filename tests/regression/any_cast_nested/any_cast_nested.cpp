#include "any_cast_nested.h"

uint64_t AnyCastNested::test_extract(uint64_t x) {
  return extract_a<uint64_t>(SigT<uint64_t, std::any>::existt(UINT64_C(1), x));
}
