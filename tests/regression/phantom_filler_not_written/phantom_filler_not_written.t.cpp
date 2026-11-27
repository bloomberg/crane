// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <phantom_filler_not_written.h>

#include <iostream>
#include <memory>

int main() {
  auto c = std::make_shared<uint64_t>(7);
  auto r = PhantomFillerNotWritten::run_count(c, 3);
  if (r != 3) {
    std::cout << "run_count: expected 3, got " << r << std::endl;
    return 1;
  }
  std::cout << "phantom_filler_not_written: all tests passed" << std::endl;
  return 0;
}
