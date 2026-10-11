// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <outer_member_shadowed_by_nested.h>
#include <cassert>

int main() {
  assert(OuterMemberShadowedByNested::shadowed == 19);
  assert(OuterMemberShadowedByNested::with_bonus == 22);
  return 0;
}
