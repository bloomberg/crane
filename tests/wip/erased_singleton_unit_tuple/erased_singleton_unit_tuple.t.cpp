#include <erased_singleton_unit_tuple.h>
#include <any>
#include <cstdio>

int main() {
  try {
    unsigned long r = check(UINT64_C(7));
    std::fprintf(stderr, "OK: check returned %lu\n", r);
    return 0;
  } catch (const std::bad_any_cast &e) {
    std::fprintf(stderr, "BUG: bad_any_cast thrown at runtime: %s\n", e.what());
    return 1;
  }
}
