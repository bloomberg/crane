#include <rec_record.h>

__attribute__((pure)) unsigned int
RecRecord::rlist_sum(const RecRecord::rlist<unsigned int> &l) {
  if (std::holds_alternative<typename RecRecord::rlist<unsigned int>::Rnil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename RecRecord::rlist<unsigned int>::Rcons>(l.v());
    return (d_a0 + rlist_sum(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int
RecRecord::rnode_depth(const RecRecord::RNode &r) {
  auto _cs = r.rn_next.has_value()
                 ? std::make_optional<RNode>((*r.rn_next)->clone())
                 : std::nullopt;
  if (_cs.has_value()) {
    const RecRecord::RNode &next = *_cs;
    return (rnode_depth(next) + 1);
  } else {
    return 1u;
  }
}
