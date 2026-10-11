#include "den_value_not_deep_erased.h"

uint64_t DenValueNotDeepErased::size(const DenValueNotDeepErased::ty &t,
                                     DenValueNotDeepErased::den n) {
  if (std::holds_alternative<typename DenValueNotDeepErased::ty::TNat>(t.v())) {
    return crane::any_cast<uint64_t>(std::move(n));
  } else {
    const auto &[a0] =
        std::get<typename DenValueNotDeepErased::ty::TList>(t.v());
    const DenValueNotDeepErased::ty &a0_value = *a0;
    return List<DenValueNotDeepErased::den>(
               crane::any_cast<List<crane::obj>>(n))
        .template fold_left<uint64_t>(
            crane_erase_fn<uint64_t>(
                [=](uint64_t acc, DenValueNotDeepErased::den x) {
                  return (acc + size(a0_value, x));
                }),
            UINT64_C(0));
  }
}

DenValueNotDeepErased::den DenValueNotDeepErased::mk(uint64_t n) {
  return List<crane::obj>(ListDef::seq(UINT64_C(0), n));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
