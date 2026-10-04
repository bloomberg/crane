// A local's last reads become moves: all of it at its one read, or each member
// at its own read when the reads are of different members.  Two whole reads,
// a member read beside a whole one, and a template that splices its argument
// twice keep their copies.
#include "last_use_places.h"

#include <cassert>

int main() {
  Big::copies = 0;
  auto s = LastUsePlaces::swap_fields(4);
  assert(s.first.v == 5 && s.second.v == 4);
  assert(Big::copies == 0);

  auto t = LastUsePlaces::twice(7);
  assert(t.first.v == 7 && t.second.v == 7);

  auto b = LastUsePlaces::both(1);
  assert(b.first.v == 1 && b.second.first.v == 1 && b.second.second.v == 2);

  assert(LastUsePlaces::dup(3) == 6);
  return 0;
}
