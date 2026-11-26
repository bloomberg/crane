#include <deque_nil_curried_element.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << DequeNilCurriedElement::result << std::endl;
  assert(DequeNilCurriedElement::result == 20);
  return 0;
}
