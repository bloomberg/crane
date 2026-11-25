// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <hk_argument_after_phantom.h>

#include <iostream>

int main() {
  auto xs = List<uint64_t>::cons(1, List<uint64_t>::nil());
  bool r = HkArgumentAfterPhantom::count_list(xs);
  std::cout << "count_list: " << r << std::endl;
  return r ? 0 : 1;
}
