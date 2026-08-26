#include <lifted_lambda_two_users.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = LiftedLambdaTwoUsers::go;
  std::cout << "go = " << r << " (want 6)" << std::endl;
  assert(r == 6);
  return 0;
}
