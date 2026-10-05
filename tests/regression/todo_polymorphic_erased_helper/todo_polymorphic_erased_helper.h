#ifndef INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
#define INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER

#include <cstdint>

struct TodoPolymorphicErasedHelper {
  template <typename T1> static T1 test_value_crane_aux(const T1 x) {
    return x;
  }

  static inline const uint64_t test_value = []() {
    return []() {
      uint64_t kept_nat = test_value_crane_aux(UINT64_C(7));
      bool kept_bool = test_value_crane_aux(true);
      return (kept_nat + (kept_bool ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
