#ifndef INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH
#define INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH

#include <cstdint>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct persistent_array {
  /// The PrimArray mapping includes the C++ runtime helper
  /// persistent_array<T> in the global namespace.  If the extracted Rocq module
  /// is also named persistent_array, Crane emits a global C++ struct with the
  /// same name as the runtime class template.  The generated C++ does not
  /// compile because the helper template and extracted module struct collide.
  static inline const persistent_array<bool> arr =
      persistent_array<bool>(int64_t(1), true);

  static inline const bool sample = arr.get(int64_t(0));
};

#endif // INCLUDED_GENERATED_PERSISTENT_ARRAY_NAME_CLASH
