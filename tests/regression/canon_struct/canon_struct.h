#ifndef INCLUDED_CANON_STRUCT
#define INCLUDED_CANON_STRUCT

#include <any>
#include <concepts>

struct Bool {
  static bool eqb(bool b1, bool b2);
};

template <typename I>
concept EqType = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::eqb(a0, a1) } -> std::convertible_to<bool>;
};

struct CanonStruct {
  using carrier = std::any;

  struct nat_eqType {
    using carrier = uint64_t;

    static bool eqb(uint64_t a0, uint64_t a1) { return a0 == a1; }
  };

  static_assert(EqType<nat_eqType>);

  struct bool_eqType {
    using carrier = bool;

    constexpr static bool eqb(bool a0, bool a1) { return Bool::eqb(a0, a1); }
  };

  static_assert(EqType<bool_eqType>);

  template <EqType _tcI0>
  static bool same(const typename _tcI0::carrier &x,
                   const typename _tcI0::carrier &y) {
    return _tcI0::eqb(x, y);
  }

  static inline const bool test_nat =
      same<nat_eqType>(UINT64_C(3), UINT64_C(5));
  static inline const bool test_bool = same<bool_eqType>(true, false);
};

#endif // INCLUDED_CANON_STRUCT
