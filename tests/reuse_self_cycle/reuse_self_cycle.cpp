#include "reuse_self_cycle.h"

uint64_t ReuseSelfCycle::length(const ReuseSelfCycle::mylist &l) {
  if (std::holds_alternative<typename ReuseSelfCycle::mylist::Mycons>(l.v())) {
    const auto &[a0, a1] =
        std::get<typename ReuseSelfCycle::mylist::Mycons>(l.v());
    return (UINT64_C(1) + length(*a1));
  } else {
    return UINT64_C(0);
  }
}

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
