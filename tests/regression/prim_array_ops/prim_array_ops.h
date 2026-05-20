#ifndef INCLUDED_PRIM_ARRAY_OPS
#define INCLUDED_PRIM_ARRAY_OPS

#include <cstdint>
#include <persistent_array.h>

struct PrimArrayOps {
  static inline const persistent_array<int64_t> test1 =
      persistent_array<int64_t>(INT64_C(5), INT64_C(12));
  static inline const int64_t test2 = test1.length();
  static inline const int64_t test3 = test1.get(INT64_C(3));
  static inline const persistent_array<int64_t> test4 =
      test1.set(INT64_C(2), INT64_C(14));
};

#endif // INCLUDED_PRIM_ARRAY_OPS
