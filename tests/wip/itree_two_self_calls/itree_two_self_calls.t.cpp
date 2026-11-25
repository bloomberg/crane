// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <itree_two_self_calls.h>

#include <iostream>

int main() {
  ItreeTwoSelfCalls::run(1000);
  std::cout << "walk(1000) returned" << std::endl;
  return 0;
}
