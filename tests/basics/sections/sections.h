#ifndef INCLUDED_SECTIONS
#define INCLUDED_SECTIONS

struct Sections {
  static uint64_t add_n(uint64_t _x0, uint64_t _x1);
  static uint64_t mul_n(uint64_t _x0, uint64_t _x1);
  static uint64_t add_five(uint64_t _x0);
  static uint64_t mul_three(uint64_t _x0);
  static uint64_t sum_ab(uint64_t _x0, uint64_t _x1);
  static uint64_t prod_ab(uint64_t _x0, uint64_t _x1);
  static uint64_t use_inner(uint64_t a);
  static inline const uint64_t final_use = use_inner(UINT64_C(5));

  template <typename T1> static T1 identity(T1 x) { return x; }

  template <typename T1> static T1 const_(T1 x, const T1 &) { return x; }

  static inline const uint64_t test_add = add_five(UINT64_C(2));
  static inline const uint64_t test_mul = mul_three(UINT64_C(4));
  static inline const uint64_t test_nested = final_use;
  static inline const uint64_t test_id = identity<uint64_t>(UINT64_C(7));
  static inline const uint64_t test_const =
      const_<uint64_t>(UINT64_C(3), UINT64_C(9));
};

#endif // INCLUDED_SECTIONS
