#include <BarFoo.h>

namespace BarFoo {

unsigned int bar_add(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int bar_only(const unsigned int n) { return (n + 1u); }

} // namespace BarFoo
