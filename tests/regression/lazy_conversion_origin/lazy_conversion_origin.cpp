#include "lazy_conversion_origin.h"

LazyConversionOrigin::stream<uint64_t> LazyConversionOrigin::from(uint64_t n) {
  return stream<uint64_t>::lazy_(
      [=]() mutable -> typename LazyConversionOrigin::stream<uint64_t>::SCons {
        return {n, from((n + 1))};
      });
}

uint64_t LazyConversionOrigin::doubled(uint64_t n) {
  return nth<uint64_t>(n, smap<uint64_t, uint64_t>(
                              [](uint64_t x) { return (x + x); },
                              from(UINT64_C(0))));
}
