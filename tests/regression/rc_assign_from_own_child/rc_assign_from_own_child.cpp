#include "rc_assign_from_own_child.h"

uint64_t RcAssignFromOwnChild::total(const RcAssignFromOwnChild::chain &c) {
  if (std::holds_alternative<typename RcAssignFromOwnChild::chain::Last>(
          c.v())) {
    const auto &[a0] =
        std::get<typename RcAssignFromOwnChild::chain::Last>(c.v());
    return a0;
  } else {
    const auto &[a0, a1] =
        std::get<typename RcAssignFromOwnChild::chain::Link>(c.v());
    return (a0 + total(*a1));
  }
}
