#include <list_cons_erasure_bleed.h>
#include <cstdio>

int main() {
  auto r = check(UINT64_C(7));
  std::fprintf(stderr, "OK: check returned %llu\n", (unsigned long long)r);
  return 0;
}
