#ifndef INCLUDED_PERSISTENT_ARRAY_MAKE_UNCLAMPED
#define INCLUDED_PERSISTENT_ARRAY_MAKE_UNCLAMPED

#include <cstdint>
#include <persistent_array.h>

struct PersistentArrayMakeUnclamped {
  static inline const persistent_array<uint64_t> huge =
      persistent_array<uint64_t>(INT64_C(9223372036854775807), UINT64_C(0));

  static inline const int64_t len = huge.length();
};

#endif // INCLUDED_PERSISTENT_ARRAY_MAKE_UNCLAMPED
