#ifndef INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH
#define INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH

#include <cstdint>
#include <persistent_array.h>

struct persistent_array_ {
  /// The PrimArray mapping includes the C++ runtime helper
  /// persistent_array<T> in the global namespace.  If the extracted Rocq module
  /// is also named persistent_array, Crane emits a global C++ struct with the
  /// same name as the runtime class template.  The generated C++ does not
  /// compile because the helper template and extracted module struct collide.
  static inline const persistent_array<bool> arr =
      persistent_array<bool>(INT64_C(1), true);

  static inline const bool sample = arr.get(INT64_C(0));
};

#endif // INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH
