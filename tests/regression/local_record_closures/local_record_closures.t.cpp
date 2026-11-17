// Calls through a local record of functions become the functions' bodies;
// an escaping record keeps its representation, and two records stay apart.
#include "local_record_closures.h"

#include <cassert>

int main() {
  using M = LocalRecordClosures;
  assert(M::use_local(5) == 6 + 5 + 10);
  auto o = M::make(3);
  assert(o.scale(4) == 12 && o.shift(4) == 7);
  assert(M::two_records(2, 5) == 3 + 10);
  return 0;
}
