// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "record_method_lifted_helper.h"

#include <iostream>

int main() {
  int status = 0;
  // total {| nats := [1; 2]; flags := [true] |} = 2 + 1
  if (RecordMethodLiftedHelper::use != 3) {
    std::cout << "use = " << RecordMethodLiftedHelper::use << ", expected 3"
              << std::endl;
    status = 1;
  }
  if (status == 0) {
    std::cout << "All record_method_lifted_helper tests passed!" << std::endl;
  }
  return status;
}
