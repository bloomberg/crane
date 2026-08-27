#include "sigt_pair_fn_payload.h"

/// WIP: A `sigT` whose payload is a pair of a value and a function emits two
/// contradictory `any_cast`s of the same pair, and the function result is left
/// as `std::any` in a `uint64_t`-returning position.
uint64_t SigtPairFnPayload::score(const SigT<std::any, std::any> &it) {
  const auto &[x, a1] = it;
  const auto &[a, f] = std::any_cast<std::pair<std::any, std::any>>(
      std::any_cast<std::pair<std::any, std::function<uint64_t(std::any)>>>(
          a1));
  return std::any_cast<std::function<std::any(std::any)>>(f)(a);
}
