#ifndef INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER
#define INCLUDED_TODO_POLYMORPHIC_ERASED_HELPER

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T1> T1 _anon_aux(const T1 x) { return x; }

struct TodoPolymorphicErasedHelper {
  static inline const unsigned int test_value = []() {
    return []() {
      unsigned int kept_nat = _anon_aux(7u);
      bool kept_bool = _anon_aux(true);
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
