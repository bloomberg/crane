#include "boxed_pair_field_conv_ctor.h"
#include <any>
#include <cassert>
#include <cstdio>

// Force [Exp0]'s converting constructor at [_U = std::any], which is what an
// erased higher-kinded chain does.  Nothing in the .v file instantiates it, so
// without this the ill-formed branch is never compiled.
static Exp0<Dt> force(const Exp0<std::any> &e) { return Exp0<Dt>(e); }

int main() {
  // The control: a boxed field whose pointee converts on its own.
  auto self = force(Exp0<std::any>::eself(
      Exp0<std::any>::ev(std::any(Dt::dp()))));
  assert(std::holds_alternative<Exp0<Dt>::ESELF>(self.v()));

  // The defect: a boxed [std::pair] field.
  auto neg = force(Exp0<std::any>::eneg(
      std::make_pair(std::any(Dt::di(Nat::s(Nat::o()))),
                     Exp0<std::any>::ev(std::any(Dt::dp())))));
  assert(std::holds_alternative<Exp0<Dt>::ENEG>(neg.v()));

  assert(std::holds_alternative<Nat::S>(Exp0<Dt>::ev(Dt::dp()).run().v()));

  printf("All boxed_pair_field_conv_ctor tests passed!\n");
  return 0;
}
