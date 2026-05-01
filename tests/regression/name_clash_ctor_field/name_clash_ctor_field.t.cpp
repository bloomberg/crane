#include <name_clash_ctor_field.h>

#include <cassert>

int main() {
  using NS = NameClashCtorField;

  assert(NS::clash1::c1(10, 20).sum_clash1() == 30u);
  assert(NS::clash2::c2a(42).get_clash2() == 42u);
  assert(NS::clash2::c2b(99).get_clash2() == 99u);
  assert(NS::box::emptybox().unbox_sum() == 0u);
  assert(NS::box::box0(NS::pair_ind::mkpair(3, 7)).unbox_sum() == 10u);

  return 0;
}
