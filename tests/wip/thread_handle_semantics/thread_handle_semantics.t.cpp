// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <thread_handle_semantics.h>
#include <cassert>

int main() {
  assert(ThreadHandleSemantics::r1 == 3);
  assert(ThreadHandleSemantics::r2 == 4);
  assert(ThreadHandleSemantics::r3 == 7);
  return 0;
}
