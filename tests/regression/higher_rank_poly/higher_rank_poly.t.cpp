// Crane bug: a rank-2 polymorphic argument.
//
// [apply_id] uses its argument at [nat] and at [bool].  Crane returns both
// results straight out of [crane::obj] with no cast, and emits a body for the
// identity lambda that is copied from the outer return type:
//   crane_erase_fn([](const auto &x) { return crane_any_cast<std::pair<Nat, bool>>(x); })

#include <higher_rank_poly.h>

#include <cassert>

static int to_int(const Nat &n) {
  int k = 0;
  const Nat *p = &n;
  while (const auto *s = std::get_if<Nat::S>(&p->v())) {
    ++k;
    p = s->a0.get();
  }
  return k;
}

int main() {
  assert(to_int(HigherRankPoly::ex.first) == 1);
  assert(HigherRankPoly::ex.second == true);
  return 0;
}
