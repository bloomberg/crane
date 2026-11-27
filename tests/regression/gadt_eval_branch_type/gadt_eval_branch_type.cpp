#include "gadt_eval_branch_type.h"

crane::obj GadtEvalBranchType::eval(const GadtEvalBranchType::expr &e) {
  if (std::holds_alternative<typename GadtEvalBranchType::expr::Lit>(e.v())) {
    const auto &[a0] = std::get<typename GadtEvalBranchType::expr::Lit>(e.v());
    return a0;
  } else if (
          std::holds_alternative<typename GadtEvalBranchType::expr::Bl>(e.v())) {
    const auto &[a0] = std::get<typename GadtEvalBranchType::expr::Bl>(e.v());
    return a0;
  } else if (
          std::holds_alternative<typename GadtEvalBranchType::expr::Ite>(e.v())) {
    const auto &[a, a1, a2] =
        std::get<typename GadtEvalBranchType::expr::Ite>(e.v());
    if (crane::any_cast<bool>(eval(*a))) {
      return eval(*a1);
    } else {
      return eval(*a2);
    }
  } else {
    const auto &[a, b] =
        std::get<typename GadtEvalBranchType::expr::PairE>(e.v());
    return std::make_pair(crane::obj(eval(*a)), crane::obj(eval(*b)));
  }
}
