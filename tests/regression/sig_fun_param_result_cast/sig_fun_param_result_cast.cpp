#include "sig_fun_param_result_cast.h"

/// A sig whose payload is a function, passed as a parameter (so its C++ type
/// is the concrete Sig<std::function<uint64_t(uint64_t)>>), must be applied
/// directly rather than through an erased-function cast.
uint64_t SigFunParamResultCast::apply_sig(
    const Sig<std::function<uint64_t(uint64_t)>> &f,
    uint64_t n) { // Precondition: (g 0) == 0
  const auto &[x] = f;
  return x(n);
}
