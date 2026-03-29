// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iife_name_clash.h>

#include <cassert>

int main() {
  auto w1 = IifeNameClash::wrapper::wrap(3);
  auto w2 = IifeNameClash::wrapper::wrap(7);
  assert(IifeNameClash::double_get(w1, w2) == 10);

  auto e = IifeNameClash::wrapper::empty();
  assert(IifeNameClash::double_get(w1, e) == 3);
  assert(IifeNameClash::double_get(e, e) == 0);
  return 0;
}
