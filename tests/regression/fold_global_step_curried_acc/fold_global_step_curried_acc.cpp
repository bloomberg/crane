#include "fold_global_step_curried_acc.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane, alongside branch_callables_curried_join.
///
/// A global step passed to fold_left whose accumulator is a function of
/// two arguments: fold_left's type variable spells the accumulator
/// curried, fold_left<fn<fn<uint64_t(bool)>(int64_t)>>, while the
/// adapter naming step as a value took it, and returned it, flat ("no
/// matching member function for call to 'fold_left'").  The adapter now
/// takes such a parameter curried, hands step a flat closure applying it
/// one argument at a time, and returns the rest curried.
uint64_t FoldGlobalStepCurriedAcc::t1(const List<uint64_t> &l) {
  return l.template fold_left<crane::fn<uint64_t(int64_t, bool)>>(
      [](crane::fn<uint64_t(int64_t, bool)> _ec0, uint64_t _ec1) {
        return [=, _ec0 = std::move(_ec0)](int64_t _ec2,
                                           bool _ec3) {
          return step(_ec0, _ec1, _ec2, _ec3);
        };
      },
      [](int64_t, bool) { return UINT64_C(7); })(INT64_C(0), true);
}

uint64_t FoldGlobalStepCurriedAcc::t2(const List<uint64_t> &l) {
  return l.template fold_left<crane::fn<uint64_t(uint64_t)>>(
      [](crane::fn<uint64_t(uint64_t)> _ec0, uint64_t _ec1) {
        return [=, _ec0 = std::move(_ec0)](uint64_t _ec2) {
          return step2(_ec0, _ec1, _ec2);
        };
      },
      [](uint64_t y) { return y; })(UINT64_C(1));
}
