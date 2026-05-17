#ifndef INCLUDED_TODO_TYPECLASS_REQUIRES
#define INCLUDED_TODO_TYPECLASS_REQUIRES

#include <concepts>

template <typename I, typename t_A>
concept Numeric = requires(t_A a0) {
  { I::to_nat_val(a0) } -> std::convertible_to<unsigned int>;
};

struct TodoTypeclassRequires {
  struct NatNumeric {
    static unsigned int to_nat_val(unsigned int n) { return n; }
  };

  static_assert(Numeric<NatNumeric, unsigned int>);

  template <typename _tcI0, typename T1>
  static unsigned int double_val(const T1 &x) {
    return (_tcI0::to_nat_val(x) + _tcI0::to_nat_val(x));
  }

  static inline const unsigned int test_result =
      double_val<NatNumeric, unsigned int>(7u);
};

#endif // INCLUDED_TODO_TYPECLASS_REQUIRES
