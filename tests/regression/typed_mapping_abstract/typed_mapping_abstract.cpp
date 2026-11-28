#include "typed_mapping_abstract.h"

std::int64_t TypedMappingAbstract::ticks(uint64_t n, std::int64_t c) {
  if (n <= 0) {
    return c;
  } else {
    uint64_t m = n - 1;
    return ticks(m, c + 1);
  }
}

uint64_t TypedMappingAbstract::count_to(uint64_t n) {
  return static_cast<uint64_t>(ticks(n, INT64_C(0)));
}

std::int64_t TypedMappingAbstract::later(std::int64_t c) { return c + 1 + 1; }
