#ifndef INCLUDED_CLASS_SUPERCLASS_EXPLICIT
#define INCLUDED_CLASS_SUPERCLASS_EXPLICIT

#include <concepts>
#include <utility>

template <typename I, typename A>
concept Base = requires {
  { I::base(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A>
concept Ext = requires {
  { I::ext(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct ClassSuperclassExplicit {
  struct bn {
    static uint64_t base(uint64_t n) { return n; }
  };

  static_assert(Base<bn, uint64_t>);

  struct en {
    using ext_base = bn;

    static uint64_t ext(uint64_t n) { return (n + UINT64_C(1)); }
  };

  static_assert(Ext<en, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Ext<_tcI0, T1>
  static uint64_t use(const T1 &x) {
    return (_tcI0::ext_base::base(x) + _tcI0::ext(x));
  }

  static inline const uint64_t go = use<en, uint64_t>(UINT64_C(3));
};

#endif // INCLUDED_CLASS_SUPERCLASS_EXPLICIT
