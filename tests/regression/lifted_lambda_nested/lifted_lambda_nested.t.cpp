#include <lifted_lambda_nested.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = LiftedLambdaNested::go;
  std::cout << "go = " << r << " (want 8)" << std::endl;
  assert(r == 8);
  return 0;
}
