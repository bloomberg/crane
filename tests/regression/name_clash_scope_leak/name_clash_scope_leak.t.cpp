#include <name_clash_scope_leak.h>

#include <cassert>

int main() {
  using NS = NameClashScopeLeak;
  using L = List<unsigned int>;

  auto nil = L::nil();
  auto l1 = L::cons(1u, L::cons(2u, L::cons(3u, nil)));
  auto l2 = L::cons(10u, L::cons(20u, nil));
  auto l3 = L::cons(100u, nil);

  // rotate
  auto r = NS::rotate(l1);
  // [1,2,3] -> [2,3,1]
  assert(std::holds_alternative<L::Cons>(r.v()));
  assert(std::get<L::Cons>(r.v()).d_a0 == 2u);

  // heads_sum
  assert(NS::heads_sum(l1, l2) == 11u);
  assert(NS::heads_sum(nil, l2) == 10u);
  assert(NS::heads_sum(nil, nil) == 0u);

  // first_two_sum
  assert(NS::first_two_sum(l1) == 3u);
  assert(NS::first_two_sum(L::cons(5u, nil)) == 5u);
  assert(NS::first_two_sum(nil) == 0u);

  // branch_let_clash
  assert(NS::branch_let_clash(nil) == 0u);
  assert(NS::branch_let_clash(L::cons(7u, nil)) == 14u);

  // triple_head
  assert(NS::triple_head(l1, l2, l3) == 111u);
  assert(NS::triple_head(nil, l2, l3) == 110u);

  // pair_match
  assert(NS::pair_match({l1, l2}) == 11u);
  assert(NS::pair_match({nil, l2}) == 10u);

  return 0;
}
