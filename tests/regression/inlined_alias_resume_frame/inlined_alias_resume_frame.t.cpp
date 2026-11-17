// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <inlined_alias_resume_frame.h>
#include <cassert>

int main() {
  // h 0 = 1, h (m + 1) = 2 * h m + m + 1.
  assert(InlinedAliasResumeFrame::h(0) == 1);
  assert(InlinedAliasResumeFrame::h(1) == 3);
  assert(InlinedAliasResumeFrame::h(2) == 8);
  assert(InlinedAliasResumeFrame::h3 == 19);
  assert(InlinedAliasResumeFrame::h(10) == 3060);
  return 0;
}
