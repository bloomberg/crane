#include <carrier_holder_file_order.h>

#include <iostream>

// Compile-only: the header has to declare the carrier holder after the
// family alias it names.
int main() {
  auto t = CarrierHolderFileOrder::first(std::monostate{});
  (void)t;
  std::cout << "carrier_holder_file_order: ok" << std::endl;
  return 0;
}
