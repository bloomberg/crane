#ifndef INCLUDED_SHADOWED_PRIM_INT
#define INCLUDED_SHADOWED_PRIM_INT

#include <cstdint>

struct ShadowedPrimInt {
  static constexpr int64_t big = INT64_C(300);
  static inline const int64_t sum = static_cast<int64_t>(
      (static_cast<uint64_t>(big) + static_cast<uint64_t>(INT64_C(1))) &
      0x7FFFFFFFFFFFFFFFULL);
};

#endif // INCLUDED_SHADOWED_PRIM_INT
