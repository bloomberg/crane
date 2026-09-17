#include <undeducible_tt_return.h>

#include <cassert>

int main() {
  // case_ on inl1 (mkA 2) runs the left handler, which returns Some 2.
  auto ab = Sum1<ReqA, ReqB, Nat>::inl1(ReqA<Nat>::mka(Nat::s(Nat::s(Nat::o()))));
  auto r = UndeducibleTtReturn::use(ab);
  assert(r.has_value());
  return 0;
}
