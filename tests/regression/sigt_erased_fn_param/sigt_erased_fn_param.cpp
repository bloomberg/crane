#include "sigt_erased_fn_param.h"

uint64_t SigtErasedFnParam::unpack(
    const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &p) {
  const auto &[x, a1] = p;
  const auto &[x0, f] = a1;
  return crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(x0));
}
