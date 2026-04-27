#include <fix_escape_capture.h>

/// A local fixpoint that captures a function parameter and is returned
/// in a pair. The fixpoint's & capture creates a dangling reference
/// to the captured parameter after the enclosing function returns.
__attribute__((pure))
std::pair<unsigned int, std::function<unsigned int(unsigned int)>>
FixEscapeCapture::make_pair_fn(unsigned int base) {
  auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *add = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*add)(x_) + 1);
    }
  };
  return std::make_pair(base, (*add));
}

/// Same pattern with a non-recursive local fixpoint to isolate the
/// capture issue from self-reference.
__attribute__((pure))
std::pair<unsigned int, std::function<unsigned int(unsigned int)>>
FixEscapeCapture::make_pair_fn2(unsigned int base) {
  auto id_add = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *id_add = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*id_add)(x_) + 1);
    }
  };
  return std::make_pair((*id_add)(base), (*id_add));
}
