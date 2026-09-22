#include "collision_wrapper_drops_child_module.h"
#include <cassert>
#include <cstdio>

namespace {

Nat nat(unsigned n) {
  Nat acc = Nat::o();
  for (unsigned i = 0; i < n; ++i) acc = Nat::s(std::move(acc));
  return acc;
}

}  // namespace

int main() {
  // [Ident.eq_dec] reaches a child of the collision wrapper through a functor
  // application; [RawIDOrd.eq_dec] is the same construction under a name
  // nothing collides with, and [Ord.compare] names its own sibling.
  const auto one = both(AstLike::Raw_id::name(nat(1)));
  assert(std::holds_alternative<Ident::Global>(one.first.v()));
  assert(one.second.first.first);    // Ident.eq_dec 1 1
  assert(one.second.first.second);   // RawIDOrd.eq_dec 1 1
  assert(!one.second.second);        // Ord.compare k k = negb (cmp k k)

  const auto two = both(AstLike::Raw_id::anon(nat(2)));
  assert(std::holds_alternative<Ident::Local>(two.first.v()));
  assert(!two.second.first.first);   // Ident.eq_dec 2 1
  assert(!two.second.first.second);  // RawIDOrd.eq_dec 2 1
  assert(!two.second.second);

  printf("All collision_wrapper_drops_child_module tests passed!\n");
  return 0;
}
