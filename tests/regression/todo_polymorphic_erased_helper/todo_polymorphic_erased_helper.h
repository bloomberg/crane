#ifndef INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
#define INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER

template <typename T1> T1 _anon_aux(const T1 x) { return x; }

struct TodoPolymorphicErasedHelper {
  static inline const uint64_t test_value = []() {
    return []() {
      uint64_t kept_nat = _anon_aux(UINT64_C(7));
      bool kept_bool = _anon_aux(true);
      return (kept_nat + (kept_bool ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
