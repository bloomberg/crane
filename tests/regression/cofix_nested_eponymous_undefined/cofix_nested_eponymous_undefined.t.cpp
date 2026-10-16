// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "cofix_nested_eponymous_undefined.h"

#include <iostream>

int main() {
  int status = 0;
  if (CofixNestedEponymousUndefined::third_of(5) != 7) {
    std::cout << "third_of(5) != 7" << std::endl;
    status = 1;
  }
  return status;
}
