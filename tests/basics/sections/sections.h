#ifndef INCLUDED_SECTIONS
#define INCLUDED_SECTIONS

struct Sections {
  static unsigned int add_n(unsigned int _x0, unsigned int _x1);
  static unsigned int mul_n(unsigned int _x0, unsigned int _x1);
  static unsigned int add_five(unsigned int _x0);
  static unsigned int mul_three(unsigned int _x0);
  static unsigned int sum_ab(unsigned int _x0, unsigned int _x1);
  static unsigned int prod_ab(unsigned int _x0, unsigned int _x1);
  static unsigned int use_inner(unsigned int a);
  static inline const unsigned int final_use = use_inner(5u);

  template <typename T1> static T1 identity(T1 x) { return x; }

  template <typename T1> static T1 const_(T1 x, const T1 &) { return x; }

  static inline const unsigned int test_add = add_five(2u);
  static inline const unsigned int test_mul = mul_three(4u);
  static inline const unsigned int test_nested = final_use;
  static inline const unsigned int test_id = identity<unsigned int>(7u);
  static inline const unsigned int test_const = const_<unsigned int>(3u, 9u);
};

#endif // INCLUDED_SECTIONS
