#include <tfunctor_alias_carrier.h>

#include <cassert>
#include <iostream>

int main() {
  // tfmap S over the record: fst of the two texps become 2 and 3.
  assert(TfunctorAliasCarrier::is_five);
  std::cout << "tfunctor_alias_carrier: ok" << std::endl;
  return 0;
}
