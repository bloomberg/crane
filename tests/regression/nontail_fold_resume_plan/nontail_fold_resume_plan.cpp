#include "nontail_fold_resume_plan.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// g4 returns Z -> list pt through a non-tail local fixpoint whose step folds
/// over the recursive result: CRANE_CHECK_IR=1 reports "resume plan: the
/// recursion plan and the finished body disagree on whether a statement resumes
/// after a recursive call".
List<NontailFoldResumePlan::pt> NontailFoldResumePlan::g4(uint64_t n80,
                                                          int64_t x0_) {
  if (n80 <= 0) {
    return List<NontailFoldResumePlan::pt>::nil();
  } else {
    uint64_t m81 = n80 - 1;
    auto go92_impl =
        [=](auto &_self_go92, List<NontailFoldResumePlan::pt> l93,
            crane::fn<List<NontailFoldResumePlan::pt>(int64_t)> acc94,
            int64_t x0_0)
             -> List<NontailFoldResumePlan::pt> {
          if (std::holds_alternative<
                  typename List<NontailFoldResumePlan::pt>::Nil>(l93.v_mut())) {
            return g4(m81, x0_0);
          } else {
            auto &[_, a1] =
                std::get<typename List<NontailFoldResumePlan::pt>::Cons>(
                    l93.v_mut());
            const List<NontailFoldResumePlan::pt> &a1_value = *a1;
            crane::fn<List<NontailFoldResumePlan::pt>(int64_t)> rv97 =
                [=, acc94 = std::move(acc94)](int64_t _pa0) {
                  return _self_go92(_self_go92, a1_value, std::move(acc94),
                                    _pa0);
                };
            return List<List<uint64_t>>::nil().template fold_right<
                crane::fn<List<NontailFoldResumePlan::pt>(int64_t)>>(
                [](List<uint64_t>,
                   crane::fn<List<NontailFoldResumePlan::pt>(int64_t)> acc100) {
                  return acc100;
                },
                std::move(rv97))(x0_0);
          }
        };
    auto go92 =
        [=, go92_impl = std::move(go92_impl)](
            List<NontailFoldResumePlan::pt> l93,
            crane::fn<List<NontailFoldResumePlan::pt>(int64_t)> acc94,
            int64_t x0_0)
             -> List<NontailFoldResumePlan::pt> {
          return go92_impl(go92_impl, std::move(l93), std::move(acc94), x0_0);
        };
    return go92(List<NontailFoldResumePlan::pt>::nil(),
                [](int64_t) { return List<NontailFoldResumePlan::pt>::nil(); },
                x0_);
  }
}
