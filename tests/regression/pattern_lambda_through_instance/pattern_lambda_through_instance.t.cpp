// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <pattern_lambda_through_instance.h>
#include <cassert>

int main() {
  // Phi false [(3, Lit true); (5, Lit false)]: 0 + (3 + 10) + 5.
  assert(PatternLambdaThroughInstance::result == 18);
  return 0;
}
