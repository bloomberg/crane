#ifndef INCLUDED_EXTRACT_DIRECTIVES
#define INCLUDED_EXTRACT_DIRECTIVES

#include <stdexcept>

struct ExtractDirectives {
  static unsigned int offset(unsigned int base, unsigned int x);
  static unsigned int scale(unsigned int base, unsigned int x);
  static unsigned int transform(unsigned int base, unsigned int x);
  static unsigned int safe_pred(unsigned int n);
  static inline const unsigned int test_offset = offset(10u, 5u);
  static inline const unsigned int test_scale = scale(3u, 4u);
  static inline const unsigned int test_transform = transform(2u, 3u);
  static inline const unsigned int test_safe_pred = safe_pred(5u);
  static unsigned int inner_add(unsigned int _x0, unsigned int _x1);
  static unsigned int inner_mul(unsigned int _x0, unsigned int _x1);
  static unsigned int outer_use(unsigned int a, unsigned int b);
  static inline const unsigned int test_inner = inner_add(3u, 7u);
  static inline const unsigned int test_outer = outer_use(4u, 5u);
};

#endif // INCLUDED_EXTRACT_DIRECTIVES
