// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// The typed-mapping checks run while the .vo is built; this only confirms
// that the extraction beside them is unaffected.
#include <typed_mapping_selection.h>

#include <iostream>

int main() {
  if (Sample::answer != 42) {
    std::cout << "Error: Sample::answer is " << Sample::answer << "\n";
    return 1;
  }
  std::cout << "All typed_mapping_selection tests passed!\n";
  return 0;
}
