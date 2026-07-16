// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "concept_param_mismatch.h"
#include <iostream>

int main() {
  auto r = ConceptParamMismatch::test;
  std::cout << (r == 6 ? "PASSED" : "FAILED") << std::endl;
  return r != 6; 
}
