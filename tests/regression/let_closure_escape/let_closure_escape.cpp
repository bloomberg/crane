#include "let_closure_escape.h"

/// BUG: let-bound partial application returned through a Box.
/// f := sum_values t creates a & lambda bound to a variable.
/// Box f stores the variable (not a direct lambda) in a constructor.
/// When let_escape returns, t is destroyed → dangling reference in Box.
LetClosureEscape::fn_box
LetClosureEscape::let_escape(LetClosureEscape::tree t) {
  crane::fn<uint64_t(uint64_t)> f =
      [=, t = std::move(t)](uint64_t _x0) -> uint64_t {
    return std::move(t).sum_values(_x0);
  };
  return fn_box::box(std::move(f));
}
