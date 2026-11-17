#include "subclass_type_projection_alias.h"

Itree<
    crane::obj, Sum<SubclassTypeProjectionAlias::Err,
                    SubclassTypeProjectionAlias::dv<
                        typename SubclassTypeProjectionAlias::natParams::ptr>>>
SubclassTypeProjectionAlias::run() {
  return run_program<SubclassTypeProjectionAlias::natParams>(
      ITree::template map<crane::obj,
                          SubclassTypeProjectionAlias::Res<
                              Nat, SubclassTypeProjectionAlias::dv<Nat>>,
                          Sum<SubclassTypeProjectionAlias::Err,
                              SubclassTypeProjectionAlias::Res<
                                  Nat, SubclassTypeProjectionAlias::dv<Nat>>>>(
          [](const std::pair<
              std::pair<SubclassTypeProjectionAlias::State<Nat>, List<Nat>>,
              SubclassTypeProjectionAlias::dv<Nat>> &x) {
            return Sum<SubclassTypeProjectionAlias::Err,
                       SubclassTypeProjectionAlias::Res<
                           Nat, SubclassTypeProjectionAlias::dv<Nat>>>::inr(x);
          },
          interp<SubclassTypeProjectionAlias::natParams>()));
}
