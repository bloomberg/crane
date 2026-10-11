#include "den_fn_ctor_arg_not_wrapped.h"

DenFnCtorArgNotWrapped::den
DenFnCtorArgNotWrapped::unbox(const DenFnCtorArgNotWrapped::ty &,
                              const DenFnCtorArgNotWrapped::box &b) {
  const auto &[a0] = b;
  return a0;
}
