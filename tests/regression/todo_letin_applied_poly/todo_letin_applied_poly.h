#ifndef INCLUDED_TODO_LETIN_APPLIED_POLY
#define INCLUDED_TODO_LETIN_APPLIED_POLY

#include <memory>
#include <optional>
#include <type_traits>

struct TodoLetinAppliedPoly {
  static inline const unsigned int demo_nat = 7u;
  static inline const bool demo_bool = true;
  static inline const unsigned int test_value = (demo_bool ? demo_nat : 0u);
};

#endif // INCLUDED_TODO_LETIN_APPLIED_POLY
