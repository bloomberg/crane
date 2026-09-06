#ifndef INCLUDED_REAL_MAPPING_GET_D
#define INCLUDED_REAL_MAPPING_GET_D

#include <crane_real.h>
#include <cstdint>

/// Mapping.Real is integer-flavor-agnostic, so a program that uses IZR
/// imports one as well -- here ZInt, which makes from_z's argument an
/// int64_t.  What remains is reading the result back out: Real wraps a
/// long double and must offer a conversion to it.
struct RealMappingGetD {
  static inline const Real x =
      (Real::from_z(INT64_C(3)) +
       (Real::from_z(INT64_C(4)) * Real::from_z(INT64_C(2))));
  static inline const Real y = (x / Real::from_z(INT64_C(2)));
  static inline const Real run = (y - Real::from_z(INT64_C(1)));
};

#endif // INCLUDED_REAL_MAPPING_GET_D
