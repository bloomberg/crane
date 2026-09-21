#include "pair_field_conv_ctor.h"
#include <any>
#include <cassert>
#include <cstdio>

// Force [Ann]'s converting constructor at [_U = std::any], which is what an
// erased higher-kinded chain does.  Nothing in the .v file instantiates it, so
// without this the ill-formed branch is never compiled.
static Ann<Dt> force(const Ann<std::any> &e) { return Ann<Dt>(e); }

int main() {
  // The control: the [list] field rebuilds, the [pair] field is the defect.
  Ann<std::any> boxed = Ann<std::any>::ann_prefix(
      texp<std::any>{std::any(Dt::di(Nat::s(Nat::o()))),
                     Exp0<std::any>::en()});
  auto back = force(boxed);
  assert(std::holds_alternative<Ann<Dt>::ANN_prefix>(back.v()));

  // [run] itself only ever needs the two concrete instantiations.
  auto r = run(Ann<Nat>::ann_metadata(
      List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil())));
  assert(std::holds_alternative<Ann<Dt>::ANN_metadata>(r.v()));

  printf("All pair_field_conv_ctor tests passed!\n");
  return 0;
}
