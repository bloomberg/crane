#ifndef INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
#define INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER

#include <any>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename T1> T1 _anon_aux(const T1 x) { return x; }

struct TodoPolymorphicErasedHelper {
  static inline const unsigned int test_value = []() {
    return [&]() {
      unsigned int kept_nat = std::any_cast<unsigned int>(aux(7u));
      bool kept_bool = std::any_cast<unsigned int>(aux(true));
      return (kept_nat + [&]() -> unsigned int {
        if (kept_bool) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
};

#endif // INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
