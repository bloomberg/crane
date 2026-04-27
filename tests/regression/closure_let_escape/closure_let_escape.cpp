#include <closure_let_escape.h>

/// A local fixpoint captures a LET-BINDING (not a function parameter)
/// and escapes through Some (std::optional).
///
/// BUG: Local fixpoints use & capture. The let-binding base is a
/// stack variable. The fixpoint escapes through Some, so
/// return_captures_by_value does NOT apply. After the function
/// returns, base is destroyed, and the captured reference dangles.
///
/// Difference from fix_escape_capture: captures a LET-BINDING
/// (not a function parameter). The let-binding involves a computation
/// (n * 2), so it can't be optimized away.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
ClosureLetEscape::make_fn_fix(const unsigned int &n) {
  unsigned int base = (n * 2u);
  auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *add = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*add)(x_) + 1);
    }
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>((*add));
}

/// test3: Captures from multiple let bindings.
/// BUG: Both a and b are captured by &, both dangle.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
ClosureLetEscape::make_fn_multi(const unsigned int &n) {
  unsigned int a = (n + 1u);
  unsigned int b = (a * 3u);
  auto helper = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *helper = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return (a + b);
    } else {
      unsigned int x_ = x - 1;
      return ((*helper)(x_) + 1);
    }
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>(
      (*helper));
}
