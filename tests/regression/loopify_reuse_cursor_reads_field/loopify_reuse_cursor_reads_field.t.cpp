// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_reuse_cursor_reads_field.h>

#include <cassert>
#include <cstdio>

using M = LoopifyReuseCursorReadsField;
using L = M::lst;

static L l123() { return L::cons(1, L::cons(2, L::cons(3, L::nil()))); }

int main() {
  // Uniquely owned lists, so the cursor recycles every cell it walks.
  // pairs [1;2;3] = [1+2; 2+1; 3+0].
  L p = M::pairs(l123());
  assert(M::len(p) == 3 && M::sum(p) == 9);
  // weigh 10 [1;2;3] = [1*10; 2*2; 3*1].
  L w = M::weigh(10, l123());
  assert(M::len(w) == 3 && M::sum(w) == 17);

  // A shared list is left as it was.
  L s = l123();
  L q = M::pairs(s);
  assert(M::sum(q) == 9 && M::sum(s) == 6);
  std::printf("loopify_reuse_cursor_reads_field: ok\n");
  return 0;
}
