#include <fix_curried_escape.h>

/// A local fixpoint that escapes through an option wrapper,
/// preventing Crane from uncurrying it away.
///
/// make_fn defines a local fixpoint go with & capture of
/// base (a stack variable).  Wrapping in Some forces
/// the fixpoint to be stored as a std::function, because the
/// return type option (nat -> nat) cannot be uncurried.
///
/// BUG: The std::function holds & references to base.
/// After make_fn returns, base is destroyed, and calling
/// the extracted function accesses freed memory.
std::optional<std::function<unsigned int(unsigned int)>>
FixCurriedEscape::make_fn(unsigned int base) {
  auto go_impl = [=](auto &_self_go, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](unsigned int x) mutable -> unsigned int {
    return go_impl(go_impl, x);
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>(go);
}
