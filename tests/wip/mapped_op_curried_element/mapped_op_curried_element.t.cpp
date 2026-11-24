#include <mapped_op_curried_element.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = MappedOpCurriedElement::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 231);
  return 0;
}
