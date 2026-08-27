// A [sig] whose payload is a function, passed as a parameter (so its C++ type
// is the concrete [Sig<std::function<uint64_t(uint64_t)>>]), must be applied
// directly rather than through an erased-function cast.
#include "sig_fun_param_result_cast.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigFunParamResultCast::go == 2);
  std::cout << "sig_fun_param_result_cast: go = " << SigFunParamResultCast::go << " PASSED" << std::endl;
  return 0;
}
