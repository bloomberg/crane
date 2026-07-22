#include <sigt_fn_any.h>

#include <any>
#include <cstdio>
#include <variant>

// Regression test for the parse-a-lot LL-parser `bad_any_cast` (now fixed).
//
// In Rocq, `check tt` evaluates to `true` — the stored predicate is
// `(fun n => n =? 0)` and it is applied to `0`. Before the fix, the extracted
// C++ threw `std::bad_any_cast`, because a function value stored into a
// `std::any` as a raw lambda closure (in `Make::mk`) was read back with
// `any_cast<std::function<std::any(std::any)>>` (in `Make::run`). `Make::mk`
// now routes the callable through `crane_erase_fn`, so the representations
// agree and `check` returns `true`.
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
    std::fprintf(stderr,
                 "BUG: bad_any_cast thrown (expected true): %s\n", e.what());
    return 1;
  }
}
