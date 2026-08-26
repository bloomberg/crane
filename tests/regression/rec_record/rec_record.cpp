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
