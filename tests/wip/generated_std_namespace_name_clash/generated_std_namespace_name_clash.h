#ifndef INCLUDED_GENERATED_STD_NAMESPACE_NAME_CLASH
#define INCLUDED_GENERATED_STD_NAMESPACE_NAME_CLASH

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct std {
  /// Standard extraction includes C++ standard library headers and emits
  /// references to namespace std.  If the extracted Rocq module is named std,
  /// Crane emits a global C++ struct std, colliding with the existing standard
  /// namespace.  The generated C++ does not compile because a namespace and a
  /// struct cannot share the same name in the global namespace.
  static inline const bool sample = true;
};

#endif // INCLUDED_GENERATED_STD_NAMESPACE_NAME_CLASH
