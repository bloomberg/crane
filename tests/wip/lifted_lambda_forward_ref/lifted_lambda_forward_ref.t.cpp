#include <lifted_lambda_forward_ref.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = LiftedLambdaForwardRef::go;
  std::cout << "go = " << r << " (want 4)" << std::endl;
  assert(r == 4);
  return 0;
}
