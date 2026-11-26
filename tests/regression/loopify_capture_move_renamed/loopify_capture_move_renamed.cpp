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
uint64_t LoopifyCaptureMoveRenamed::partition_cps(
    crane::fn<bool(uint64_t)> p, const List<uint64_t> &l,
    crane::fn<uint64_t(List<uint64_t>, List<uint64_t>)> k) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  crane::fn<uint64_t(List<uint64_t>, List<uint64_t>)> _loop_k = std::move(k);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_k(List<uint64_t>::nil(), List<uint64_t>::nil());
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      const List<uint64_t> &a1_value = *a1;
      _loop_k =
          [=, _loop_k = std::move(_loop_k)](const List<uint64_t> &yes,
                                            const List<uint64_t> &no)
               -> uint64_t {
            if (p(a0)) {
              return _loop_k(List<uint64_t>::cons(a0, yes), no);
            } else {
              return _loop_k(yes, List<uint64_t>::cons(a0, no));
            }
          };
      _loop_l = &a1_value;
    }
  }
}

uint64_t LoopifyCaptureMoveRenamed::count_evens(const List<uint64_t> &l) {
  return partition_cps(
      Nat::even, l,
      [](const List<uint64_t> &yes, List<uint64_t>) { return yes.length(); });
}

uint64_t LoopifyCaptureMoveRenamed::count_odds(const List<uint64_t> &l) {
  return partition_cps(
      Nat::even, l, [](List<uint64_t>,
                       const List<uint64_t> &eta0_) { return eta0_.length(); });
}

bool Nat::even(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return true;
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        return false;
      } else {
        uint64_t n_ = n0 - 1;
        n = n_;
      }
    }
  }
}
