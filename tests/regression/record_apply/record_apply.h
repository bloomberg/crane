#ifndef INCLUDED_RECORD_APPLY
#define INCLUDED_RECORD_APPLY

#include "fn.h"
#include <cstdint>

struct RecordApply {
  struct R {
    crane::fn<uint64_t(uint64_t, uint64_t)> f;
    uint64_t tag_;
  };

  static uint64_t apply_record(const R &r0, uint64_t a, uint64_t b);
  static inline const R r =
      R{[](uint64_t x, uint64_t) { return x; }, UINT64_C(3)};
  static constexpr uint64_t three = UINT64_C(3);
};

#endif // INCLUDED_RECORD_APPLY
