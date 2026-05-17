#ifndef INCLUDED_TODO_ERASED_INSTANCE_PARAM
#define INCLUDED_TODO_ERASED_INSTANCE_PARAM

#include <concepts>

template <typename I, typename A>
concept Default = requires {
  { I::def() } -> std::convertible_to<A>;
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
