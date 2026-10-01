#include <nested_class_state_arg.h>

#include <cassert>
#include <iostream>

int main() {
  assert(NestedClassStateArg::is_three);
  std::cout << "nested_class_state_arg: ok" << std::endl;
  return 0;
}
