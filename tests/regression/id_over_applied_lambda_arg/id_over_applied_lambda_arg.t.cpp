#include <id_over_applied_lambda_arg.h>

#include <cstdint>
#include <iostream>

int main() {
  int fails = 0;
  uint64_t c = IdOverAppliedLambdaArg::control(4);
  std::cout << "control 4 = " << c << std::endl;
  if (c != 5) ++fails;
  uint64_t a = IdOverAppliedLambdaArg::one_arg(4);
  std::cout << "one_arg 4 = " << a << std::endl;
  if (a != 5) ++fails;
  uint64_t b = IdOverAppliedLambdaArg::two_args(4);
  std::cout << "two_args 4 = " << b << std::endl;
  if (b != 5) ++fails;
  return fails == 0 ? 0 : 1;
}
