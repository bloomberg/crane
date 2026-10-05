#include "reuse_self_cycle.h"

uint64_t ReuseSelfCycle::length(const ReuseSelfCycle::mylist &l) {
  {
    const ReuseSelfCycle::mylist &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const ReuseSelfCycle::mylist *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename ReuseSelfCycle::mylist::Mycons>(
              _lc1_loop_l0->v())) {
        const auto &[a0, a1] =
            std::get<typename ReuseSelfCycle::mylist::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
        _lc1_loop_l0 = crane_raw(a1);
      } else {
        return _lc1_loop_acc;
      }
    }
  }
}

/// BUG: The reuse optimization fires and sets d_a1 = l, where l
/// is the scrutinee (the very node being mutated).
/// This creates a CYCLE: the node's tail points to itself.
///
/// In Rocq, mycons x l creates a FRESH cons cell whose tail is l.
/// With reuse, the SAME cell is mutated: d_a1 <- l makes the cell
/// point to itself.
///
/// Calling length on the result causes infinite recursion -> stack overflow.
///
/// Reuse fires because:
/// 1. l escapes in else l -> owned
/// 2. mycons branch tail is mycons with arity 2 = 2
/// 3. mycons is index 0 -> List.hd picks it
/// 4. use_count() == 1 for fresh values
ReuseSelfCycle::mylist ReuseSelfCycle::prepend_self(ReuseSelfCycle::mylist l,
                                                    bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseSelfCycle::mylist::Mycons>(
            l.v_mut())) {
      auto &[a0, a1] =
          std::get<typename ReuseSelfCycle::mylist::Mycons>(l.v_mut());
      return mylist::mycons(a0, l);
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
