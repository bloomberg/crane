#include "sig_fun_param_result_cast.h"

/// A sig whose payload is a function, passed as a parameter (so its C++ type
/// is the concrete Sig<std::function<uint64_t(uint64_t)>>), must be applied
/// directly rather than through an erased-function cast.
uint64_t
SigFunParamResultCast::apply_sig(const crane::fn<uint64_t(uint64_t)> &x0_,
                                 uint64_t x1_) {
  // Precondition: (g 0) == 0
  return x0_(x1_);
}
