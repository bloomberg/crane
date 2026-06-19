#include "DequeElementCast.h"

#include "Specif.h"

namespace DequeElementCast {

uint64_t DequeElementCast::count_items(
    const Specif::SigT<DequeElementCast::Nonterm, std::any> &e) {
  const auto &[x0, a1] = e;
  switch (x0) {
  case Nonterm::NT_ITEM: {
    return UINT64_C(0);
  }
  case Nonterm::NT_ITEMS: {
    return static_cast<uint64_t>(
        std::any_cast<std::deque<std::any>>(a1).size());
  }
  default:
    std::unreachable();
  }
}

uint64_t DequeElementCast::get_item_num(
    const Specif::SigT<DequeElementCast::Nonterm, std::any> &e) {
  const auto &[x0, a1] = e;
  switch (x0) {
  case Nonterm::NT_ITEM: {
    auto &&_sv0 = std::any_cast<DequeElementCast::Val>(a1);
    if (std::holds_alternative<typename DequeElementCast::Val::VNum>(
            _sv0.v())) {
      const auto &[n0] =
          std::get<typename DequeElementCast::Val::VNum>(_sv0.v());
      return n0;
    } else {
      const auto &[s0] =
          std::get<typename DequeElementCast::Val::VStr>(_sv0.v());
      return (s0 + UINT64_C(100));
    }
    break;
  }
  case Nonterm::NT_ITEMS: {
    return UINT64_C(0);
  }
  default:
    std::unreachable();
  }
}

} // namespace DequeElementCast
