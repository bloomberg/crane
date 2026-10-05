#ifndef INCLUDED_POLY_ID_AT_FUNCTION_TYPE
#define INCLUDED_POLY_ID_AT_FUNCTION_TYPE

#include "fn.h"
#include <cstdint>

struct PolyIdAtFunctionType {
  /// A polymorphic identity instantiated at a function type collapses the
  /// two levels of application into a single call on a one-argument
  /// std::function.
  template <typename T1> static T1 id2(T1 x) { return x; }

  static uint64_t apply_id(uint64_t n);
  static uint64_t apply_id2(uint64_t n);
  static constexpr uint64_t total = UINT64_C(23);
};

#endif // INCLUDED_POLY_ID_AT_FUNCTION_TYPE
