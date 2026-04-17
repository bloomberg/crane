#include <function_return_branch_probe.h>

#include <cassert>
#include <iostream>

static unsigned int nat_to_uint(const std::shared_ptr<Nat> &n) {
  unsigned int acc = 0;
  const Nat *cur = n.get();
  while (std::holds_alternative<Nat::S>(cur->v())) {
    ++acc;
    cur = std::get<Nat::S>(cur->v()).d_a0.get();
  }
  return acc;
}

int main() {
  // This test reproduces a bug where a recursive function returning a lambda
  // from multiple match branches causes Crane to emit an inner IIFE lambda
  // with no explicit return type.  C++ cannot deduce a common return type
  // from two distinct closure types, so the generated code fails to compile:
  //
  //   error: return type '(lambda at ...)' must match previous return type
  //   '(lambda at ...)' when lambda expression has unspecified explicit return type
  //
  // If this compiles and runs, the bug is fixed.
  unsigned int result = nat_to_uint(FunctionReturnBranchProbe::sample);
  // make_adder 2 40 = 42
  std::cout << "sample = " << result << std::endl;
  assert(result == 42u);

  return 0;
}
