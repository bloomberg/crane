#ifndef INCLUDED_TODO_ERASED_INSTANCE_PARAM
#define INCLUDED_TODO_ERASED_INSTANCE_PARAM

#include <concepts>

template <typename I, typename A>
concept Default = requires {
  { I::def() } -> std::convertible_to<A>;
};

struct TodoErasedInstanceParam {
  struct natDefault {
    static uint64_t def() { return UINT64_C(4); }
  };

  static_assert(Default<natDefault, uint64_t>);

  template <typename _tcI0, typename T1> static T1 pick() {
    return _tcI0::def();
  }

  static inline const uint64_t test_value =
      (pick<natDefault, uint64_t>() + pick<natDefault, uint64_t>());
};

#endif // INCLUDED_TODO_ERASED_INSTANCE_PARAM
