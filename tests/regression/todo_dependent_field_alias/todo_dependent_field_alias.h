#ifndef INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
#define INCLUDED_TODO_DEPENDENT_FIELD_ALIAS

#include <any>
#include <concepts>
#include <functional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a0, a1) } -> std::convertible_to<typename I::carrier>;
};

struct TodoDependentFieldAlias {
  using carrier = std::any;

  struct nat_magma {
    using carrier = unsigned int;

    constexpr static unsigned int op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }
  };

  static_assert(Magma<nat_magma>);

  template <Magma _tcI0>
  __attribute__((pure)) static typename _tcI0::carrier
  pick_op(const typename _tcI0::carrier _x0,
          const typename _tcI0::carrier _x1) {
    return _tcI0::op(_x0, _x1);
  }

  static inline const unsigned int test_value = []() {
    std::function<unsigned int(unsigned int, unsigned int)> alias =
        [](unsigned int _x0, unsigned int _x1) -> unsigned int {
      return pick_op<nat_magma>(_x0, _x1);
    };
    return alias(2u, 3u);
  }();
};

#endif // INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
