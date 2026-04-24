#include <fix_curried_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

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
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
FixCurriedEscape::make_fn(unsigned int base) {
  auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *go = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*go)(x_) + 1);
    }
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>((*go));
}
