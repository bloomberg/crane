#include "hk_carrier_binder_at_concrete_site.h"
#include <cassert>
#include <cstdio>

int main() {
  // [run] traverses a [holder nat (box nat)] through a non-generic instance,
  // which is the site that has no binder in scope.  [3 <? 4] holds, [3 <? 0]
  // does not, so the two fields come out different and neither is skipped.
  holder<Nat, box<Nat>> m{Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                          box<Nat>{Nat::o()}};
  auto r = run(m);
  assert(r.h_head);
  assert(!r.h_body.b_payload);
  printf("All hk_carrier_binder_at_concrete_site tests passed!\n");
  return 0;
}
