#include "sigt_pair_fn_payload.h"

/// A sigT whose payload is a pair of a value and a function: both pair
/// components are boxed at the producer -- the function through the
/// erased-callable adapter -- so the consumer recovers the pair with a single
/// any_cast<pair<any,any>> and applies the callable.
uint64_t SigtPairFnPayload::score(
    const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &it) {
  const auto &[x, a1] = it;
  const auto &[a, f] = a1;
  return crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(a));
}
