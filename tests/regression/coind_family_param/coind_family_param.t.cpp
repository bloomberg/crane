#include <coind_family_param.h>

#include <cassert>
#include <iostream>

int main() {
  // count 10 0 takes ten Taus and returns 10; 100 fuel is plenty.
  assert(CoindFamilyParam::is_ten);
  std::cout << "coind_family_param: ok" << std::endl;
  return 0;
}
