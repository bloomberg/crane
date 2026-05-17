#include "SepExtDoubleTypename.h"

#include <cassert>

int main() {
  struct NatOrd { using t = uint64_t; };

  using FMap = SepExtDoubleTypename::FMapList<NatOrd>;
  using List = Datatypes::List<std::pair<uint64_t, int>>;

  // Test is_empty on empty list
  auto empty = List::nil();
  assert(FMap::is_empty(empty) == true);

  // Test is_empty on non-empty list
  auto one = List::cons(std::pair<uint64_t, int>{UINT64_C(1), 42}, List::nil());
  assert(FMap::is_empty(one) == false);

  // Test head_key
  auto key = FMap::head_key(one);
  assert(key.has_value());
  assert(key.value() == UINT64_C(1));

  // Test head_key on empty
  auto no_key = FMap::head_key(empty);
  assert(!no_key.has_value());

  return 0;
}
