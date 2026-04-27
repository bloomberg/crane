#include <fix_higher_order.h>

/// Creates a fixpoint and passes it through wrap_fn.
/// The fixpoint escapes through the function call, not through
/// direct constructor application.
///
/// BUG HYPOTHESIS: When the fixpoint is passed as an argument to
/// wrap_fn, the translation may use & capture. wrap_fn stores
/// it in Some and returns. After make_wrapped returns, the
/// captured base is destroyed.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
FixHigherOrder::make_wrapped(unsigned int base) {
  auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *go = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*go)(x_) + 1);
    }
  };
  return wrap_fn((*go));
}

__attribute__((pure))
std::optional<std::optional<std::function<unsigned int(unsigned int)>>>
FixHigherOrder::make_double_wrapped(unsigned int base) {
  auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *go = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*go)(x_) + 1);
    }
  };
  return double_wrap((*go));
}
