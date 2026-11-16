#include "pair_field_conv_ctor.h"

Ann<Dt> run(const Ann<Nat> &a) {
  return TFunctor_ann::template tfmap<Nat, Dt>(
      [](const Nat &n) { return Dt::di(n); }, a);
}
