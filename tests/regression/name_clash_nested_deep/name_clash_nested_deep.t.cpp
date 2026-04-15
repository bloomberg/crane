#include <name_clash_nested_deep.h>

#include <cassert>

int main() {
  using NS = NameClashNestedDeep;

  auto nil = NS::mylist::mynil();
  auto mk = [](unsigned int h, auto t) { return NS::mylist::mycons(h, t); };

  auto l1 = mk(10, nil);
  auto l2 = mk(20, nil);
  auto l3 = mk(30, nil);
  auto l4 = mk(40, nil);

  assert(NS::deep4(nil, nil, nil, nil) == 0u);
  assert(NS::deep4(l1, nil, nil, nil) == 10u);
  assert(NS::deep4(l1, l2, nil, nil) == 30u);
  assert(NS::deep4(l1, l2, l3, nil) == 60u);
  assert(NS::deep4(l1, l2, l3, l4) == 100u);

  assert(NS::let_match_chain(l1, l2) == 30u);
  assert(NS::let_match_chain(nil, l2) == 20u);

  auto l12 = mk(10, mk(20, nil));
  assert(NS::multi_match_same(l12) == 30u);
  assert(NS::multi_match_same(l1) == 10u);
  assert(NS::multi_match_same(nil) == 0u);

  auto l123 = mk(10, mk(20, mk(30, nil)));
  assert(NS::nested_field_match(nil) == 0u);
  assert(NS::nested_field_match(l1) == 1u);
  assert(NS::nested_field_match(l12) == 2u);
  assert(NS::nested_field_match(l123) == 30u);

  return 0;
}
