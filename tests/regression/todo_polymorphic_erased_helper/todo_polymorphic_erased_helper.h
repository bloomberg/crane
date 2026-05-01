#ifndef INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
#define INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER

#include <memory>
#include <optional>
#include <type_traits>

template <typename T1> T1 _anon_aux(const T1 x) { return x; }

struct TodoPolymorphicErasedHelper {
  static inline const unsigned int test_value = []() {
    return []() {
      unsigned int kept_nat = _anon_aux(7u);
      bool kept_bool = _anon_aux(true);
      return (kept_nat + (kept_bool ? 1u : 0u));
    }();
  }();
};

#endif // INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
