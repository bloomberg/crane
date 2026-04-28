#ifndef INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
#define INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct TodoExplicitTypeAppAlias {
  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const unsigned int test_value = []() {
    return []() {
      unsigned int kept_nat = id(9u);
      bool kept_bool = id(true);
      return (kept_nat + (kept_bool ? 1u : 0u));
    }();
  }();
};

#endif // INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
