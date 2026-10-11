// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <list_literal_lambda_mapped_result.h>
#include <cassert>

int main() {
  assert(ListLiteralLambdaMappedResult::from_option == 4);
  assert(ListLiteralLambdaMappedResult::from_pair == 3);
  return 0;
}
