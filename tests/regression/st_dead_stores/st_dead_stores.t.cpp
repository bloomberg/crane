// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <st_dead_stores.h>

#include <iostream>

namespace {
int failures = 0;
void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAILED: " << what << std::endl;
    ++failures;
  }
}
} // namespace

int main() {
  using M = StDeadStores;
  check(M::written_only == 7, "written_only = 7");
  check(M::read_by_dead_store == 0, "read_by_dead_store = 0");
  check(M::written_in_branch(true) == 11, "written_in_branch true = 11");
  check(M::written_in_branch(false) == 12, "written_in_branch false = 12");
  check(M::written_in_unused_branch(true) == 4, "written_in_unused_branch true = 4");
  check(M::written_in_unused_branch(false) == 3, "written_in_unused_branch false = 3");
  if (failures == 0) {
    std::cout << "st_dead_stores: all tests passed" << std::endl;
  }
  return failures;
}
