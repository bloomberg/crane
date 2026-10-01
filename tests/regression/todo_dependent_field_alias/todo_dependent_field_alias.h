#ifndef INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
#define INCLUDED_TODO_DEPENDENT_FIELD_ALIAS

#include "obj.h"
#include <any>
#include <concepts>
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
  using carrier = crane::obj;

  struct nat_magma {
    using carrier = uint64_t;

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Magma<nat_magma>);

  template <Magma _tcI0>
  static typename _tcI0::carrier pick_op(const typename _tcI0::carrier &x0_,
                                         const typename _tcI0::carrier &x1_) {
    return _tcI0::op(x0_, x1_);
  }

  static inline const uint64_t test_value =
      crane::any_cast<uint64_t>(pick_op<nat_magma>(UINT64_C(2), UINT64_C(3)));
};

#endif // INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
