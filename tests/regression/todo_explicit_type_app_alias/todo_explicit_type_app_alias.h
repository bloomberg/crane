#ifndef INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
#define INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS

#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct TodoExplicitTypeAppAlias {
  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const unsigned int test_value = []() {
    return []() {
      unsigned int kept_nat = id(9u);
      bool kept_bool = id(true);
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

#endif // INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
