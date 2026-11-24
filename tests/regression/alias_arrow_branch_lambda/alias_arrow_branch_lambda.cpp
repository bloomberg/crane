#include "alias_arrow_branch_lambda.h"

AliasArrowBranchLambda::st<uint64_t>
AliasArrowBranchLambda::g(bool b, const List<uint64_t> &x0_) {
  return List<uint64_t>::nil().template fold_left<
      crane::fn<AliasArrowBranchLambda::st<uint64_t>(List<uint64_t>)>>(
      [](
          crane::fn<crane::fn<std::pair<uint64_t, uint64_t>(uint64_t)>(
              List<uint64_t>)> acc,
          uint64_t) { return acc; },
      [&]() -> crane::fn<AliasArrowBranchLambda::st<uint64_t>(List<uint64_t>)> {
        if (b) {
          return [](List<uint64_t>) { return sret<uint64_t>(UINT64_C(6)); };
        } else {
          uint64_t k = UINT64_C(4);
          return [=](List<uint64_t>) { return sret<uint64_t>(k); };
        }
      }())(x0_);
}
