#ifndef INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH
#define INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH

#include <cstdint>
#include <persistent_array.h>

struct persistent_array_ {
  static inline const persistent_array<bool> arr =
      persistent_array<bool>(INT64_C(1), true);

  static inline const bool sample = arr.get(INT64_C(0));
};

#endif // INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH
