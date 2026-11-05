#include <lent_alias_by_reference.h>

#include <cassert>
#include <iostream>

int main() {
  using L = LentAliasByReference;

  assert(L::test_size == 4u);
  assert(L::test_big_size == 5u);
  assert(L::test_sum == 10u);
  assert(L::test_lookup_hit == 20u);
  assert(L::test_lookup_miss == 99u);
  // [1;2;3;4] . [5;1;2;3] = 5 + 2 + 6 + 12
  assert(L::test_dot == 25u);

  // Lent through the abbreviation, the caller's bag is untouched.
  L::bag b = L::sample;
  assert(L::bag_size(b) == 4u);
  assert(L::bag_sum(b) == 10u);
  assert(L::bag_size(b) == 4u);

  std::cout << "All lent_alias_by_reference tests passed!" << std::endl;
  return 0;
}
