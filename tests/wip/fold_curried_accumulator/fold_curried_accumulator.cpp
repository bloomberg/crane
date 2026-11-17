#include "fold_curried_accumulator.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// fold_left whose accumulator is a two-argument function: the step lambda's
/// accumulator parameter is spelled flat (crane::fn<uint64_t(uint64_t,
/// uint64_t)>)
/// while fold_left's T1 is the curried
/// crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>,
/// so the requires clause rejects the call.
uint64_t FoldCurriedAccumulator::g(const List<uint64_t> &l, uint64_t x0_,
                                   uint64_t x1_) {
  return l.template fold_left<
      crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>>(
      [](crane::fn<uint64_t(uint64_t, uint64_t)> acc, uint64_t e) {
        return [=, acc = std::move(acc)](uint64_t x) {
          return [=](uint64_t y) { return acc(y, (x + e)); };
        };
      },
      [](uint64_t x) {
        return [=](uint64_t) { return x; };
      })(x0_)(x1_);
}
