#ifndef INCLUDED_POLY_ID_AT_FUNCTION_TYPE
#define INCLUDED_POLY_ID_AT_FUNCTION_TYPE

#include <functional>

struct PolyIdAtFunctionType {
  /// A polymorphic identity instantiated at a function type collapses the
  /// two levels of application into a single call on a one-argument
  /// std::function.
  template <typename T1> static T1 id2(T1 x) { return x; }

  static uint64_t apply_id(uint64_t n);
  static uint64_t apply_id2(uint64_t n);
  static inline const uint64_t total =
      (apply_id(UINT64_C(4)) + apply_id2(UINT64_C(2)));
};

#endif // INCLUDED_POLY_ID_AT_FUNCTION_TYPE
