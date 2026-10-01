#include <carrier_holder_before_alias.h>

#include <cassert>
#include <iostream>

int main() {
  assert(CarrierHolderBeforeAlias::is_three);
  std::cout << "carrier_holder_before_alias: ok" << std::endl;
  return 0;
}
