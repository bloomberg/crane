#include "sigt_erased_fn_param.h"

uint64_t SigtErasedFnParam::unpack(
    const SigT<std::any, std::pair<std::any, std::any>> &p) {
  const auto &[x, a1] = p;
  const auto &[x0, f] = a1;
  return std::any_cast<uint64_t>(
      std::any_cast<std::function<std::any(std::any)>>(f)(x0));
}
