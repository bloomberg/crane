// WIP: this test does not build yet.
//
// A `sig` whose payload is a function, passed as a *parameter* (so its C++
// type is the concrete `Sig<std::function<uint64_t(uint64_t)>>`), is still
// applied through `any_cast<std::function<std::any(std::any)>>`, so the call
// yields `std::any` where `uint64_t` is required.
#include "sig_fun_param_result_cast.h"

#include <cassert>
#include <iostream>

int main() {
  assert(SigFunParamResultCast::go == 2);
  std::cout << "sig_fun_param_result_cast: go = " << SigFunParamResultCast::go << " PASSED" << std::endl;
  return 0;
}
