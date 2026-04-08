#include <cps_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using CE = CpsEscape;

  // cps_escape: make_adder creates [&] lambda with std::move(t)->make_adder(x).
  // operator-> doesn't consume unique_ptr, so single call works.
  // Expected: tree_sum(t) + 5 = 60 + 5 = 65
  auto r1 = CE::cps_escape;
  std::cout << "cps_escape = " << r1 << std::endl;
  assert(r1 == 65u);

  // cps_escape_inline: same but closure goes directly to store_in_box
  auto r2 = CE::cps_escape_inline;
  std::cout << "cps_escape_inline = " << r2 << std::endl;
  assert(r2 == 65u);

  // cps_escape_two: two adders from different trees
  // Expected: tree_sum(t1) + tree_sum(t2) = 60 + 100 = 160
  auto r3 = CE::cps_escape_two;
  std::cout << "cps_escape_two = " << r3 << std::endl;
  assert(r3 == 160u);

  std::cout << "All cps_escape tests passed!" << std::endl;
  return 0;
}
