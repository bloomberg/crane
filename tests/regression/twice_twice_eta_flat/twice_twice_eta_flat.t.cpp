#include <twice_twice_eta_flat.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << TwiceTwiceEtaFlat::result << std::endl;
  assert(TwiceTwiceEtaFlat::result == 8);
  return 0;
}
