#include "loopify_capture_move_renamed.h"

/// A continuation captured by move, in a function loopified.
///
/// partition_cps hands the recursive call a new continuation that closes
/// over the old one, k, for the last time: the closure takes k by move.
/// Loopified, k becomes the loop variable _loop_k, and the closure is
/// written over it at every turn.  The closure's reads were renamed but its
/// capture move was not, so it went on moving from k, which the loop had
/// already moved into _loop_k on entry: a read of a moved-from value, and
/// the continuation it did read copied.
uint64_t LoopifyCaptureMoveRenamed::count_evens(const List<uint64_t> &l) {
  return partition_cps(
      Nat::even, l,
      [](const List<uint64_t> &yes, List<uint64_t>) { return yes.length(); });
}

uint64_t LoopifyCaptureMoveRenamed::count_odds(const List<uint64_t> &l) {
  return partition_cps(Nat::even, l,
                       [](List<uint64_t>, const List<uint64_t> &eta0_) {
                         return eta0_.length();
                       });
}

bool Nat::even(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return true;
    } else {
      uint64_t n0 = _loop_n - 1;
      if (n0 <= 0) {
        return false;
      } else {
        uint64_t n_ = n0 - 1;
        _loop_n = n_;
      }
    }
  }
}
