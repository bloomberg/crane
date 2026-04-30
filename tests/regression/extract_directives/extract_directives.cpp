#include <extract_directives.h>

unsigned int ExtractDirectives::offset(const unsigned int &base,
                                       const unsigned int &x) {
  return (x + base);
}

unsigned int ExtractDirectives::scale(const unsigned int &base,
                                      const unsigned int &x) {
  return (x * base);
}

unsigned int ExtractDirectives::transform(const unsigned int &base,
                                          const unsigned int &x) {
  return scale(base, offset(base, x));
}

unsigned int ExtractDirectives::safe_pred(const unsigned int &n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = n - 1;
    return n0;
  }
}

unsigned int ExtractDirectives::inner_add(const unsigned int &_x0,
                                          const unsigned int &_x1) {
  return (_x0 + _x1);
}

unsigned int ExtractDirectives::inner_mul(const unsigned int &_x0,
                                          const unsigned int &_x1) {
  return (_x0 * _x1);
}

unsigned int ExtractDirectives::outer_use(const unsigned int &a,
                                          const unsigned int &b) {
  return (inner_add(a, b) + inner_mul(a, b));
}
