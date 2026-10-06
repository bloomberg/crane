#include "hk_dict_from_constraint_param.h"

holder<Nat, List<Nat>>
HkDictFromConstraintParam::run(const holder<Nat, List<Nat>> &m) {
  return TFunctor_holder<TFunctor_list, TFunctor_box>::template tfmap<Nat, Nat>(
      [](const Nat &x) { return Nat::s(x); }, m);
}
