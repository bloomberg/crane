#include <sigt_prod_fn_any.h>

#include <any>
#include <cstdio>
#include <variant>

// Regression test for the parse-a-lot LL-parser `bad_any_cast` in the
// product-payload case (now fixed).
//
// In Rocq, `check tt` evaluates to `true`: the stored predicate `(fun n => n =? 0)`
// applied to `0` holds.
//
// Before the fix, the extracted C++ threw `std::bad_any_cast`: the two functions
// were stored as raw lambda closures via `std::make_pair(std::any(f),
// std::any(g))` but read back with `any_cast<std::function<std::any(std::any)>>`.
// The fix extends `crane_erase_fn` wrapping to function values boxed into erased
// fields through a custom constructor (here `std::pair`), so `mk` now emits
// `std::make_pair(crane_erase_fn(f), crane_erase_fn(g))` and the read matches.
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
