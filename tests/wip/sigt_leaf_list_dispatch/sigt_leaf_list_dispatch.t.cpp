#include <sigt_leaf_list_dispatch.h>
#include <any>
#include <cstdio>
#include <variant>

int main() {
  try {
    bool r = check(std::monostate{});
    if (!r) {
      std::fprintf(stderr, "FAIL: check returned false (expected true)\n");
      return 1;
    }
    std::fprintf(stderr, "OK: check returned true\n");
    return 0;
  } catch (const std::bad_any_cast &e) {
    std::fprintf(stderr, "BUG: bad_any_cast thrown (expected true): %s\n", e.what());
    return 1;
  }
}
