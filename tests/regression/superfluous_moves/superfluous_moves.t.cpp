// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression test for issue #74: superfluous moves in monadic branches.

#include <superfluous_moves.h>

namespace {
int testStatus = 0;
}

#define ASSERT(X)                                                              \
  {                                                                            \
    if (!(X)) {                                                                \
      std::cerr << "Error " __FILE__ ":" << __LINE__ << " '" << #X            \
                << "' failed." << std::endl;                                   \
      testStatus = 1;                                                          \
    }                                                                          \
  }

int main() {
  auto result = SuperfluousMoves::bad_branch(SuperfluousMoves::sample_loop);
  ASSERT(result.first == false);
  return testStatus;
}
