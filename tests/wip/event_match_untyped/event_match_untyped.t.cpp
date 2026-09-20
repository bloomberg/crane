#include "event_match_untyped.h"
#include <cassert>
#include <variant>

int main() {
  // Reaching the Vis branch is not the point -- the defect is that the
  // translation unit does not compile.  A Ret is enough to link.
  auto n = EventMatchUntyped::weight(ITree<Nat>::ret(Nat::s(Nat::o())));
  assert(std::holds_alternative<typename Nat::S>(n.v()));
  return 0;
}
