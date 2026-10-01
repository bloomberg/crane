#include <ret_in_iter_lambda.h>

#include <iostream>

int main() {
  auto c = RetInIterLambda::c;
  (void)c;
  std::cout << "ret_in_iter_lambda: ok" << std::endl;
  return 0;
}
