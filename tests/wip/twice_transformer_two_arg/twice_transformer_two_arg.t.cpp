#include <twice_transformer_two_arg.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << TwiceTransformerTwoArg::result << std::endl;
  assert(TwiceTransformerTwoArg::result == 22);
  return 0;
}
