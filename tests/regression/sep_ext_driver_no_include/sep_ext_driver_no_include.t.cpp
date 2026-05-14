// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: an extraction driver .v file with no definitions of its own
// must not cause a spurious #include "SepExtDriverNoInclude.h" in the
// generated header for the extracted module.

#include "SepExtDriverNoInclude.h"

int main() {
  const auto v = SepExtDriverNoInclude::Content::x;
  (void)v;
  return 0;
}
