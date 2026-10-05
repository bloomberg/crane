#include "hk_carrier_binder_at_concrete_site.h"

box<crane::obj> TFunctor_box(const crane::fn<crane::obj(crane::obj)> &f,
                             const box<crane::obj> &b) {
  return box<crane::obj>{f(b.b_payload)};
}

template <typename CraneTcArg>
using crane_carrier_tc_c3f54f3304e568f5 = holder<CraneTcArg, box<CraneTcArg>>;

holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m) {
  return convert<crane_carrier_tc_c3f54f3304e568f5>(
      Convert_holder, Nat::s(Nat::s(Nat::s(Nat::o()))), m);
}
