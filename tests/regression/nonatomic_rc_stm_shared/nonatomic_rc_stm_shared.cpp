#include "nonatomic_rc_stm_shared.h"

uint64_t NonatomicRcStmShared::len(const NonatomicRcStmShared::lst &l) {
  if (std::holds_alternative<typename NonatomicRcStmShared::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename NonatomicRcStmShared::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}

stm::TVar<NonatomicRcStmShared::lst> NonatomicRcStmShared::make() {
  return stm::atomically(
      [&] { return stm::newTVar<NonatomicRcStmShared::lst>(lst::nil()); });
}

void NonatomicRcStmShared::push(stm::TVar<NonatomicRcStmShared::lst> t,
                                uint64_t n) {
  {
    stm::atomically([&] {
      return [&]() {
        NonatomicRcStmShared::lst l = stm::readTVar(t);
        stm::writeTVar(t, lst::cons(n, std::move(l)));
        return std::monostate{};
      }();
    });
    return;
  }
}

uint64_t NonatomicRcStmShared::size(stm::TVar<NonatomicRcStmShared::lst> t) {
  return stm::atomically([&] {
    return [&]() {
      NonatomicRcStmShared::lst l = stm::readTVar(t);
      return len(std::move(l));
    }();
  });
}
