#include "sig_fun_param_result_cast.h"

/// WIP: A `sig` whose payload is a function, passed as a *parameter* (so its
/// C++ type is the concrete `Sig<std::function<uint64_t(uint64_t)>>`), is still
/// applied through `any_cast<std::function<std::any(std::any)>>`, so the call
/// yields `std::any` where `uint64_t` is required.
uint64_t SigFunParamResultCast::apply_sig(
    const Sig<std::function<uint64_t(uint64_t)>> &f,
    uint64_t n) { // Precondition: (g 0) == 0
  assert(true);
  const auto &[x] = f;
  return std::any_cast<std::function<std::any(std::any)>>(x)(n);
}
