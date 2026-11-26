#include <nested_curried_instantiation.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << NestedCurriedInstantiation::result << std::endl;
  assert(NestedCurriedInstantiation::result == 8);
  std::cout << "result2 = " << NestedCurriedInstantiation::result2 << std::endl;
  assert(NestedCurriedInstantiation::result2 == 44);
  std::cout << "result3 = " << NestedCurriedInstantiation::result3 << std::endl;
  assert(NestedCurriedInstantiation::result3 == 7);
  return 0;
}
