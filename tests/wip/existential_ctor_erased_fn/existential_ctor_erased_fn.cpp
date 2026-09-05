#include "existential_ctor_erased_fn.h"

uint64_t
ExistentialCtorErasedFn::read(const ExistentialCtorErasedFn::dynamic &d) {
  const auto &[a, a1] = d;
  return a1(a);
}
