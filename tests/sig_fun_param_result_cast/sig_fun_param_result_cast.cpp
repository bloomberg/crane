#include "sig_fun_param_result_cast.h"

uint64_t SigFunParamResultCast::apply_sig(
    const Sig<std::function<uint64_t(uint64_t)>> &f,
    uint64_t n) { // Precondition: (g 0) == 0
  assert(true);
  const auto &[x] = f;
  return x(n);
}
