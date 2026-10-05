#include "let_pair_shadow.h"

uint64_t LetPairShadow::mylist_sum(const LetPairShadow::mylist<uint64_t> &l) {
  {
    const LetPairShadow::mylist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const LetPairShadow::mylist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<
              typename LetPairShadow::mylist<uint64_t>::Mynil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename LetPairShadow::mylist<uint64_t>::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// Helper functions that return pairs (force temporary allocation).
std::pair<uint64_t, uint64_t> LetPairShadow::add_pair(uint64_t a, uint64_t b) {
  return std::make_pair((a + b), (a * b));
}

std::pair<uint64_t, uint64_t> LetPairShadow::sub_pair(uint64_t a, uint64_t b) {
  return std::make_pair((((a - b) > a ? 0 : (a - b))), (a + b));
}

/// Pattern 2: Two destructs of function-call results in top-level body.
uint64_t LetPairShadow::double_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                             uint64_t d) {
  auto [sum_ab, prod_ab] = add_pair(a, b);
  auto [diff_cd, sum_cd] = sub_pair(c, d);
  return (((sum_ab + prod_ab) + diff_cd) + sum_cd);
}

/// Pattern 3: Three destructs of function-call results.
uint64_t LetPairShadow::triple_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                             uint64_t d, uint64_t e,
                                             uint64_t f) {
  auto [r1, r2] = add_pair(a, b);
  auto [r3, r4] = add_pair(c, d);
  auto [r5, r6] = add_pair(e, f);
  return (((((r1 + r2) + r3) + r4) + r5) + r6);
}
