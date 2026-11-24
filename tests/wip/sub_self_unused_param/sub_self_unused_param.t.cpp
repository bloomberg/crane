#include <sub_self_unused_param.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = SubSelfUnusedParam::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 7);
  return 0;
}
