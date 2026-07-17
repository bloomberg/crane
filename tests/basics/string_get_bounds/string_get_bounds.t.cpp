// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <string_get_bounds.h>

#include <iostream>

int main() {
  int status = 0;

  // In-bounds indexing returns the expected character.
  if (StringGetBounds::first != 'a') {
    std::cout << "FAIL: PrimString.get in-bounds\n";
    status = 1;
  }
  if (StringGetBounds::sv_first != 'a') {
    std::cout << "FAIL: sv_get in-bounds\n";
    status = 1;
  }

  // Out-of-range indexing returns the null char (Rocq's total [get]
  // semantics) instead of performing an out-of-bounds read.
  if (StringGetBounds::oob != '\0') {
    std::cout << "FAIL: PrimString.get out-of-bounds should be '\\0'\n";
    status = 1;
  }
  if (StringGetBounds::sv_oob != '\0') {
    std::cout << "FAIL: sv_get out-of-bounds should be '\\0'\n";
    status = 1;
  }

  if (status == 0) {
    std::cout << "string_get_bounds: all checks passed\n";
  }
  return status;
}
