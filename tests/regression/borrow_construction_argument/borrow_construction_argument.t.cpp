#include <borrow_construction_argument.h>

#include <cassert>
#include <iostream>

using C = BorrowConstructionArgument;

int main() {
  // Ordinary functional behavior still holds.
  C::big b{1, 2, 3, 4};
  auto [v, s] = C::run(b);
  assert(v == 5u);
  assert(s.b1 == 1 && s.b2 == 2 && s.b3 == 3 && s.b4 == 4);

  // ret's lambda now borrows its state parameter: calling it through a
  // held-by-reference caller costs exactly one copy (inside make_pair),
  // not two (one into the lambda's own by-value parameter, another into
  // make_pair).
  auto k = C::Monad_stateT::ret<uint64_t>(7);
  C::big b2{10, 20, 30, 40};
  auto [s2, v2] = k(b2);
  assert(v2 == 7u);
  assert(s2.b1 == 10 && s2.b4 == 40);
  // b2 is untouched -- confirms the call borrowed, not moved from, it.
  assert(b2.b1 == 10 && b2.b4 == 40);

  std::cout << "All borrow_construction_argument tests passed!" << std::endl;
  return 0;
}
