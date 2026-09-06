#include "currying.h"

uint64_t Currying::add3(uint64_t a, uint64_t b, uint64_t c) {
  return (a + (b + c));
}

uint64_t Currying::add3_partial1(uint64_t x0_, uint64_t x1_) {
  return add3(UINT64_C(1), x0_, x1_);
}

uint64_t Currying::add3_partial2(uint64_t x0_) {
  return add3(UINT64_C(1), UINT64_C(2), x0_);
}

uint64_t Currying::pair_add(const Currying::pair<uint64_t, uint64_t> &p) {
  const auto &[a0, a1] = p;
  return (a0 + a1);
}

uint64_t Currying::curried_add(uint64_t x0_, uint64_t x1_) {
  return curry<uint64_t, uint64_t, uint64_t>(pair_add, x0_, x1_);
}

uint64_t Currying::uncurried_add3(
    const Currying::pair<uint64_t, Currying::pair<uint64_t, uint64_t>> &p) {
  const auto &[a0, a1] = p;
  const auto &[a00, a10] = a1;
  return add3(a0, a00, a10);
}

uint64_t Currying::sub(uint64_t x0_, uint64_t x1_) {
  return (((x0_ - x1_) > x0_ ? 0 : (x0_ - x1_)));
}

uint64_t Currying::flipped_sub(uint64_t x0_, uint64_t x1_) {
  return flip<uint64_t, uint64_t, uint64_t>(sub, x0_, x1_);
}

uint64_t Currying::add_base(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }

uint64_t Currying::add_ten(uint64_t x0_) {
  return add_base((UINT64_C(2) * UINT64_C(5)), x0_);
}
