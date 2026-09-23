#include "hk_carrier_binder_at_concrete_site.h"

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b) {
  return box<std::any>{f(b.b_payload)};
}

template <typename _CraneTcArg>
using _crane_carrier_tc_904911fedcfba566 =
    holder<_CraneTcArg, box<_CraneTcArg>>;

holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m) {
  return convert<_crane_carrier_tc_904911fedcfba566>(
      Convert_holder, Nat::s(Nat::s(Nat::s(Nat::o()))), m);
}
