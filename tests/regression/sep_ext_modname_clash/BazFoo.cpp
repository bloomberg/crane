#include <BazFoo.h>

namespace BazFoo {

unsigned int baz_add(const unsigned int n, const unsigned int m) {
  return ((n + m) + 1u);
}

unsigned int baz_only(const unsigned int n) { return (n + 2u); }

} // namespace BazFoo
