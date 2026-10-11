// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <projection_result_overapplied.h>
#include <cassert>

int main() {
  assert(ProjectionResultOverapplied::direct == 5);
  assert(ProjectionResultOverapplied::through_definition == 5);
  assert(ProjectionResultOverapplied::second == 40);
  return 0;
}
