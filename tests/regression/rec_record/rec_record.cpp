#include "rec_record.h"

uint64_t RecRecord::rlist_sum(const RecRecord::rlist<uint64_t> &l) {
  if (std::holds_alternative<typename RecRecord::rlist<uint64_t>::Rnil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename RecRecord::rlist<uint64_t>::Rcons>(l.v());
    return (a0 + rlist_sum(*a1));
  }
}

uint64_t RecRecord::rnode_depth(const RecRecord::RNode &r) {
  auto _cs = r.rn_next.has_value() ? std::make_optional<RNode>(**r.rn_next)
                                   : std::nullopt;
  if (_cs.has_value()) {
    const RecRecord::RNode &next = *_cs;
    return (rnode_depth(next) + 1);
  } else {
    return UINT64_C(1);
  }
}
