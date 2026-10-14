// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "wrapper_instance_lifted_helper.h"

#include <iostream>

int main() {
  int status = 0;
  // size ([1; 2], [true]) + twice 1 = (2 + 1) + 2
  if (WrapperInstanceLiftedHelper::use != 5) {
    std::cout << "use = " << WrapperInstanceLiftedHelper::use << ", expected 5"
              << std::endl;
    status = 1;
  }
  if (status == 0) {
    std::cout << "All wrapper_instance_lifted_helper tests passed!" << std::endl;
  }
  return status;
}
