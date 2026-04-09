#include <let_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// BUG: let-bound partial application returned through a Box.
/// f := sum_values t creates a & lambda bound to a variable.
/// Box f stores the variable (not a direct lambda) in a constructor.
/// When let_escape returns, t is destroyed → dangling reference in Box.
std::shared_ptr<LetClosureEscape::fn_box>
LetClosureEscape::let_escape(std::shared_ptr<LetClosureEscape::tree> t) {
  std::function<unsigned int(unsigned int)> f =
      [=](unsigned int _x0) mutable -> unsigned int {
    return t->sum_values(_x0);
  };
  return fn_box::box(f);
}
