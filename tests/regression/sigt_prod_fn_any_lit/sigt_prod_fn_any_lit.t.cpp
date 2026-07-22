#include <sigt_prod_fn_any_lit.h>

#include <any>
#include <cstdio>
#include <variant>

// Minimal reproduction of the parse-a-lot LL-parser `bad_any_cast`, now fixed.
//
// In Rocq, `check tt` is `true` (predicate `0 =? 0`). The predicate/action
// lambdas are inline generic literals (`[](const auto&){...}`) stored into an
// erased `std::pair<std::any,std::any>` payload via a custom constructor.
// `gen_expr_custom_cons` now routes such function-valued lambda args through
// `crane_erase_fn` (which dispatches on whether `std::function` CTAD is
// viable, falling back to a direct any->any wrap for generic lambdas), so the
// stored `std::any` matches what `any_cast<std::function<std::any(std::any)>>`
// expects on read.
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
