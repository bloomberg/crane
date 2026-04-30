#ifndef INCLUDED_TODO_ERASED_INSTANCE_PARAM
#define INCLUDED_TODO_ERASED_INSTANCE_PARAM

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename I, typename t_A>
concept Default = requires {
  { I::def() } -> std::convertible_to<t_A>;
};

struct TodoErasedInstanceParam {
  struct natDefault {
    static unsigned int def() { return 4u; }
  };

  static_assert(Default<natDefault, unsigned int>);

  template <typename _tcI0, typename T1> static T1 pick() {
    return _tcI0::def();
  }

  static inline const unsigned int test_value =
      (pick<natDefault, unsigned int>() + pick<natDefault, unsigned int>());
};

#endif // INCLUDED_TODO_ERASED_INSTANCE_PARAM
