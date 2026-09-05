#include "erased_pair_fn_call.h"

uint64_t ErasedPairFnCall::size(
    const SigT<std::any, std::pair<List<std::any>, std::any>> &b) {
  const auto &[x, a1] = b;
  const auto &[l, f] = a1;
  return std::any_cast<uint64_t>(
      std::any_cast<std::function<std::any(std::any)>>(f)(l));
}
