#include "loopify_continue_moves_local.h"

/// A tail loop moves a local of its turn into a parameter's next value
/// where the turn owns it and reads it there for the last time
/// (Ownership_ir.continue_moves, Move_argument): where nothing reads it
/// after but the Continue's other arguments, by name, it is moved at the
/// last of the loop's updates that reads it.  A part of it read by another
/// argument keeps it copied.
List<uint64_t> LoopifyContinueMovesLocal::count_down(uint64_t n,
                                                     List<uint64_t> acc) {
  List<uint64_t> _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      List<uint64_t> next = List<uint64_t>::cons(m, std::move(_loop_acc));
      _loop_acc = std::move(next);
      _loop_n = m;
    }
  }
}

/// next is read by the count as well, which is updated first.
std::pair<List<uint64_t>, uint64_t>
LoopifyContinueMovesLocal::count_both(uint64_t n, const List<uint64_t> &acc,
                                      uint64_t k) {
  uint64_t _loop_k = k;
  List<uint64_t> _loop_acc = acc;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return std::make_pair(_loop_acc, _loop_k);
    } else {
      uint64_t m = _loop_n - 1;
      List<uint64_t> next = List<uint64_t>::cons(m, _loop_acc);
      _loop_k = (_loop_k + next.length());
      _loop_acc = std::move(next);
      _loop_n = m;
    }
  }
}

/// The local is passed to one parameter, its tail, computed by a call
/// on it, to another.
std::pair<List<uint64_t>, List<uint64_t>>
LoopifyContinueMovesLocal::split_off(uint64_t n, const List<uint64_t> &acc,
                                     const List<uint64_t> &rest) {
  List<uint64_t> _loop_rest = rest;
  List<uint64_t> _loop_acc = acc;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return std::make_pair(_loop_acc, _loop_rest);
    } else {
      uint64_t m = _loop_n - 1;
      List<uint64_t> next = List<uint64_t>::cons(m, _loop_acc);
      _loop_rest = next.tl();
      _loop_acc = std::move(next);
      _loop_n = m;
    }
  }
}

/// The local is passed to one parameter, the tail its match binds to
/// another: a part of it, read by name only there, so it is copied.
std::pair<List<uint64_t>, List<uint64_t>>
LoopifyContinueMovesLocal::peel(uint64_t n, const List<uint64_t> &acc,
                                const List<uint64_t> &rest) {
  List<uint64_t> _loop_rest = rest;
  List<uint64_t> _loop_acc = acc;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return std::make_pair(_loop_acc, _loop_rest);
    } else {
      uint64_t m = _loop_n - 1;
      List<uint64_t> next = List<uint64_t>::cons(m, _loop_acc);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(next.v_mut())) {
        return std::make_pair(_loop_acc, _loop_rest);
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(next.v_mut());
        _loop_rest = List<uint64_t>(*a1);
        _loop_acc = next;
        _loop_n = m;
      }
    }
  }
}
