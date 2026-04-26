#include <sprop.h>

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
SPropTest::guarded_pred(const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    return m;
  }
}

__attribute__((pure)) unsigned int
SPropTest::safe_div(const unsigned int &_x0, const unsigned int &_x1) {
  return (_x1 ? _x0 / _x1 : 0);
}
