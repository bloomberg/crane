#include <let_pair_shadow.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int LetPairShadow::mylist_sum(
    const std::shared_ptr<LetPairShadow::mylist<unsigned int>> &l) {
  if (std::holds_alternative<
          typename LetPairShadow::mylist<unsigned int>::Mynil>(l->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename LetPairShadow::mylist<unsigned int>::Mycons>(l->v());
    return (d_a0 + mylist_sum(d_a1));
  }
}

/// Helper functions that return pairs (force temporary allocation).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LetPairShadow::add_pair(const unsigned int a, const unsigned int b) {
  return std::make_pair((a + b), (a * b));
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
LetPairShadow::sub_pair(const unsigned int a, const unsigned int b) {
  return std::make_pair((((a - b) > a ? 0 : (a - b))), (a + b));
}

/// Pattern 2: Two destructs of function-call results in top-level body.
__attribute__((pure)) unsigned int
LetPairShadow::double_call_destruct(const unsigned int a, const unsigned int b,
                                    const unsigned int c,
                                    const unsigned int d) {
  auto _cs = add_pair(a, b);
  const unsigned int &sum_ab = _cs.first;
  const unsigned int &prod_ab = _cs.second;
  auto _cs1 = sub_pair(c, d);
  const unsigned int &diff_cd = _cs1.first;
  const unsigned int &sum_cd = _cs1.second;
  return (((sum_ab + prod_ab) + diff_cd) + sum_cd);
}

/// Pattern 3: Three destructs of function-call results.
__attribute__((pure)) unsigned int LetPairShadow::triple_call_destruct(
    const unsigned int a, const unsigned int b, const unsigned int c,
    const unsigned int d, const unsigned int e, const unsigned int f) {
  auto _cs = add_pair(a, b);
  const unsigned int &r1 = _cs.first;
  const unsigned int &r2 = _cs.second;
  auto _cs1 = add_pair(c, d);
  const unsigned int &r3 = _cs1.first;
  const unsigned int &r4 = _cs1.second;
  auto _cs2 = add_pair(e, f);
  const unsigned int &r5 = _cs2.first;
  const unsigned int &r6 = _cs2.second;
  return (((((r1 + r2) + r3) + r4) + r5) + r6);
}
