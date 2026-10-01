#include "erased_pair_fn_call.h"

uint64_t ErasedPairFnCall::size(
    const SigT<crane::obj, std::pair<List<crane::obj>, crane::obj>> &b) {
  const auto &[x, a1] = b;
  const auto &[l, f] = a1;
  return crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(l));
}
