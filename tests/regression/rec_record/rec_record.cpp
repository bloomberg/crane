#include "rec_record.h"

uint64_t RecRecord::rlist_sum(const RecRecord::rlist<uint64_t> &l) {
  {
    const RecRecord::rlist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const RecRecord::rlist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename RecRecord::rlist<uint64_t>::Rnil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename RecRecord::rlist<uint64_t>::Rcons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}
