// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <stm_tvar_of_function.h>
#include <cassert>

int main() {
  assert(StmTvarOfFunction::created() == 1);
  assert(StmTvarOfFunction::written() == 3);
  return 0;
}
