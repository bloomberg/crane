#include <grammar_tuple_record_cons.h>
#include <cstdio>
#include <variant>

int main() {
  // Reaching here means the extracted grammar entries compiled at all.
  unsigned long n = num_entries(std::monostate{});
  std::fprintf(stderr, "OK: num_entries = %lu\n", n);
  return n == 2 ? 0 : 1;
}
