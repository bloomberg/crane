#ifndef INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
#define INCLUDED_TODO_DEPENDENT_FIELD_ALIAS

#include <any>
#include <concepts>
#include <functional>
#include <utility>

template <typename I>
concept Magma = requires {
  typename I::carrier;
  {
    I::op(std::declval<typename I::carrier>(),
          std::declval<typename I::carrier>())
  } -> std::convertible_to<typename I::carrier>;
};

struct TodoDependentFieldAlias {
  using carrier = std::any;

  struct nat_magma {
    using carrier = uint64_t;

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Magma<nat_magma>);

  template <Magma _tcI0>
  static typename _tcI0::carrier pick_op(const typename _tcI0::carrier &_x0,
                                         const typename _tcI0::carrier &_x1) {
    return _tcI0::op(_x0, _x1);
  }

  static inline const uint64_t test_value = []() {
    std::function<uint64_t(uint64_t, uint64_t)> alias =
        [](uint64_t _x0, uint64_t _x1) -> uint64_t {
      return pick_op<nat_magma>(_x0, _x1);
    };
    return alias(UINT64_C(2), UINT64_C(3));
  }();
};

#endif // INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
