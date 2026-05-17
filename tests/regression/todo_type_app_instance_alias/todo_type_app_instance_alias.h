#ifndef INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS
#define INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS

#include <concepts>

template <typename I, typename A>
concept Boxed = requires {
  { I::boxed_default() } -> std::convertible_to<A>;
};

struct TodoTypeAppInstanceAlias {
  struct natBoxed {
    static unsigned int boxed_default() { return 7u; }
  };

  static_assert(Boxed<natBoxed, unsigned int>);

  template <typename _tcI0, typename T1> static T1 pick() {
    return _tcI0::boxed_default();
  }

  static inline const unsigned int test_value = []() {
    return (pick<natBoxed, unsigned int>() + pick<natBoxed, unsigned int>());
  }();
};

#endif // INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS
