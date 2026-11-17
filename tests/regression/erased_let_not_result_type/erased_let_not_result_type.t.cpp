// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <erased_let_not_result_type.h>
#include <cassert>

int main() {
  // 7 (unique) + 107 (ambig) + 1001 (reject).
  assert(ErasedLetNotResultType::run == 7 + 107 + 1001);
  return 0;
}
