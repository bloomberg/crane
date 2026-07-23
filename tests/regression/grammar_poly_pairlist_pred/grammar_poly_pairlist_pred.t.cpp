#include <grammar_poly_pairlist_pred.h>
#include <cstdio>
#include <variant>

int main() {
  unsigned long n = num_entries(std::monostate{});
  std::fprintf(stderr, "OK: num_entries = %lu\n", n);
  return n == 2 ? 0 : 1;
}
