#include "hk_carrier_binder_at_concrete_site.h"

box<crane::obj> TFunctor_box(crane::fn<crane::obj(crane::obj)> f,
                             const box<crane::obj> &b) {
  return box<crane::obj>{f(b.b_payload)};
}

template <typename _CraneTcArg>
using _crane_carrier_tc_904911fedcfba566 =
    holder<_CraneTcArg, box<_CraneTcArg>>;

holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m) {
  return convert<_crane_carrier_tc_904911fedcfba566>(
      Convert_holder, Nat::s(Nat::s(Nat::s(Nat::o()))), m);
}
