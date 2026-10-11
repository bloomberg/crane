// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <lifted_let_lambda_polymorphic.h>
#include <cassert>

int main() {
  assert(LiftedLetLambdaPolymorphic::from_let == 8);
  assert(LiftedLetLambdaPolymorphic::from_section == 4);
  return 0;
}
