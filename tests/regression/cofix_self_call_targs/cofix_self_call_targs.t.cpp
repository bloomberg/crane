#include <cofix_self_call_targs.h>

#include <cassert>
#include <iostream>

int main() {
  assert(CofixSelfCallTargs::is_three);
  std::cout << "cofix_self_call_targs: ok" << std::endl;
  return 0;
}
