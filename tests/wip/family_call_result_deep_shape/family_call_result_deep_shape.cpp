#include "family_call_result_deep_shape.h"

uint64_t FamilyCallResultDeepShape::sz(const FamilyCallResultDeepShape::ty &t,
                                       FamilyCallResultDeepShape::den n) {
  if (std::holds_alternative<typename FamilyCallResultDeepShape::ty::TNat>(
          t.v())) {
    return crane::any_cast<uint64_t>(std::move(n));
  } else if (std::holds_alternative<
                 typename FamilyCallResultDeepShape::ty::TPair>(t.v())) {
    const auto &[a0, a1] =
        std::get<typename FamilyCallResultDeepShape::ty::TPair>(t.v());
    return (
        sz(*a0, crane::any_cast<std::pair<crane::obj, crane::obj>>(n).first) +
        sz(*a1, crane::any_cast<std::pair<crane::obj, crane::obj>>(n).second));
  } else {
    const auto &[a0] =
        std::get<typename FamilyCallResultDeepShape::ty::TList>(t.v());
    const FamilyCallResultDeepShape::ty &a0_value = *a0;
    return List<FamilyCallResultDeepShape::den>(
               crane::any_cast<List<crane::obj>>(n))
        .template fold_left<uint64_t>(
            [=](uint64_t acc, FamilyCallResultDeepShape::den x) {
              return (acc + sz(a0_value, x));
            },
            UINT64_C(0));
  }
}

FamilyCallResultDeepShape::den FamilyCallResultDeepShape::mk(uint64_t n) {
  return List<crane::obj>(
      ListDef::seq(UINT64_C(0), n)
          .template map<std::pair<uint64_t, uint64_t>>(
              [](uint64_t k) { return std::make_pair(k, k); }));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
