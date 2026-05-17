#include "extract_directives.h"

unsigned int ExtractDirectives::offset(unsigned int base, unsigned int x) {
  return (x + base);
}

unsigned int ExtractDirectives::scale(unsigned int base, unsigned int x) {
  return (x * base);
}

unsigned int ExtractDirectives::transform(unsigned int base, unsigned int x) {
  return scale(base, offset(base, x));
}

unsigned int ExtractDirectives::safe_pred(unsigned int n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = n - 1;
    return n0;
  }
}

unsigned int ExtractDirectives::inner_add(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int ExtractDirectives::inner_mul(unsigned int _x0, unsigned int _x1) {
  return (_x0 * _x1);
}

unsigned int ExtractDirectives::outer_use(unsigned int a, unsigned int b) {
  return (inner_add(a, b) + inner_mul(a, b));
}
