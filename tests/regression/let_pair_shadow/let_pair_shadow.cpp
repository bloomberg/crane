#include "let_pair_shadow.h"

uint64_t LetPairShadow::mylist_sum(const LetPairShadow::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename LetPairShadow::mylist<uint64_t>::Mynil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename LetPairShadow::mylist<uint64_t>::Mycons>(l.v());
    return (a0 + mylist_sum(*a1));
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
  auto _cs = add_pair(a, b);
  uint64_t sum_ab = std::move(_cs.first);
  uint64_t prod_ab = std::move(_cs.second);
  auto _cs1 = sub_pair(c, d);
  uint64_t diff_cd = std::move(_cs1.first);
  uint64_t sum_cd = std::move(_cs1.second);
  return (((sum_ab + prod_ab) + diff_cd) + sum_cd);
}

/// Pattern 3: Three destructs of function-call results.
uint64_t LetPairShadow::triple_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                             uint64_t d, uint64_t e,
                                             uint64_t f) {
  auto _cs = add_pair(a, b);
  uint64_t r1 = std::move(_cs.first);
  uint64_t r2 = std::move(_cs.second);
  auto _cs1 = add_pair(c, d);
  uint64_t r3 = std::move(_cs1.first);
  uint64_t r4 = std::move(_cs1.second);
  auto _cs2 = add_pair(e, f);
  uint64_t r5 = std::move(_cs2.first);
  uint64_t r6 = std::move(_cs2.second);
  return (((((r1 + r2) + r3) + r4) + r5) + r6);
}
