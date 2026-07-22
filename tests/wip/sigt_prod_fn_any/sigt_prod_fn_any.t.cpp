#include <sigt_prod_fn_any.h>

#include <any>
#include <cstdio>
#include <variant>

// Minimal reproduction of the parse-a-lot LL-parser `bad_any_cast` that
// survives the `crane_erase_fn` store-site fix.
//
// In Rocq, `check tt` evaluates to `true`: the stored predicate `(fun n => n =? 0)`
// applied to `0` holds.
//
// The extracted C++ instead throws `std::bad_any_cast`, because the two
// functions are stored as raw lambda closures via `std::make_pair(std::any(f),
// std::any(g))` (no `crane_erase_fn`) but read back with
// `any_cast<std::function<std::any(std::any)>>`.
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
    std::fprintf(stderr, "BUG: bad_any_cast thrown (expected true): %s\n",
                 e.what());
    return 1;
  }
}
