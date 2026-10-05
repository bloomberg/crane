#ifndef INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS
#define INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS

#include <concepts>
#include <cstdint>

template <typename I, typename A>
concept Boxed = requires {
  { I::boxed_default() } -> std::convertible_to<A>;
};

struct TodoTypeAppInstanceAlias {
  struct natBoxed {
    constexpr static uint64_t boxed_default() { return UINT64_C(7); }
  };

  static_assert(Boxed<natBoxed, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Boxed<_tcI0, T1>
  static T1 pick() {
    return _tcI0::boxed_default();
  }

  static constexpr uint64_t test_value = UINT64_C(14);
};

#endif // INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS
