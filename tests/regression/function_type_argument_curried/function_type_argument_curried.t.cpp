// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <function_type_argument_curried.h>
#include <cassert>

int main() {
  assert(FunctionTypeArgumentCurried::result == 3 + 7 + 13 + 5);
  return 0;
}
