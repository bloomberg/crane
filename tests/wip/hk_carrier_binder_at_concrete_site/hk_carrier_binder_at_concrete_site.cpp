#include "hk_carrier_binder_at_concrete_site.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = holder<_CraneTcArg, box<_CraneTcArg>>;

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b) {
  return box<std::any>{f(b.b_payload)};
}

holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m) {
  return convert<_crane_carrier_tc>(Convert_holder,
                                    Nat::s(Nat::s(Nat::s(Nat::o()))), m);
}
