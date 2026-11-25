#include <twice_fn_transformer_step.h>
#include <iostream>
int main() {
  std::cout << TwiceFnTransformerStep::result << std::endl;
  return TwiceFnTransformerStep::result == 30 ? 0 : 1;
}
