#include <mapped_op_view_argument.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = MappedOpViewArgument::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 6);
  return 0;
}
