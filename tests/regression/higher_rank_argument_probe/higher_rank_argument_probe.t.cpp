#include <higher_rank_argument_probe.h>

#include <cassert>
#include <iostream>

int main() {
  // This test reproduces a bug where a higher-rank function argument
  //   f : forall A : Type, A -> A
  // is extracted as a lambda returning std::any, but the call site returns
  // that std::any directly from a function whose C++ return type is concrete
  // (Bool0), causing a compile error:
  //   no viable conversion from returned value of type 'std::any'
  //   to function return type 'Bool0'
  //
  // If this compiles and runs, the bug is fixed.
  auto r = HigherRankArgumentProbe::sample;
  // call_poly f = f bool true, with f = identity, so result is true
  std::cout << "sample = " << (r == Bool0::e_TRUE0 ? "true" : "false") << std::endl;
  assert(r == Bool0::e_TRUE0);

  return 0;
}
