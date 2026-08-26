#ifndef INCLUDED_CLASS_SUPERCLASS_FIELD
#define INCLUDED_CLASS_SUPERCLASS_FIELD

#include <concepts>
#include <utility>

template <typename I, typename A>
concept Eqb = requires {
  { I::eqb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};
template <typename I, typename A>
concept Ord = requires {
  { I::le(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};

struct ClassSuperclassField {
  struct eqnat {
    static bool eqb(uint64_t a0, uint64_t a1) { return a0 == a1; }
  };

  static_assert(Eqb<eqnat, uint64_t>);

  struct ordnat {
    using ord_eq = eqnat;

    static bool le(uint64_t a0, uint64_t a1) { return a0 <= a1; }
  };

  static_assert(Ord<ordnat, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Ord<_tcI0, T1>
  static uint64_t cmp(const T1 &x, const T1 &y) {
    if (_tcI0::ord_eq::eqb(x, y)) {
      return UINT64_C(0);
    } else {
      if (_tcI0::le(x, y)) {
        return UINT64_C(1);
      } else {
        return UINT64_C(2);
      }
    }
  }

  static inline const uint64_t go =
      cmp<ordnat, uint64_t>(UINT64_C(1), UINT64_C(2));
};

#endif // INCLUDED_CLASS_SUPERCLASS_FIELD
