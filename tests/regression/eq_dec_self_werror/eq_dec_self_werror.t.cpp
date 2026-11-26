#include <eq_dec_self_werror.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << EqDecSelfWerror::result << std::endl;
  assert(EqDecSelfWerror::result == 1);
  return 0;
}
