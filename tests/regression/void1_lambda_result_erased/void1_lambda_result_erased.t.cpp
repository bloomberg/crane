#include <void1_lambda_result_erased.h>

#include <cassert>
#include <iostream>

int main() {
  // step (4, 0) = Ret (inl (3, 1)), so first = 3.
  assert(Void1LambdaResultErased::is_three);
  std::cout << "void1_lambda_result_erased: ok" << std::endl;
  return 0;
}
