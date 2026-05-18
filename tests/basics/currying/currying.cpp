#include "currying.h"

uint64_t Currying::add3(uint64_t a, uint64_t b, uint64_t c) {
  return (a + (b + c));
}

uint64_t Currying::add3_partial1(uint64_t _x0, uint64_t _x1) {
  return add3(UINT64_C(1), _x0, _x1);
}

uint64_t Currying::add3_partial2(uint64_t _x0) {
  return add3(UINT64_C(1), UINT64_C(2), _x0);
}

uint64_t Currying::pair_add(const Currying::pair<uint64_t, uint64_t> &p) {
  const auto &[a0, a1] = p;
  return (a0 + a1);
}

uint64_t Currying::curried_add(uint64_t _x0, uint64_t _x1) {
  return curry<uint64_t, uint64_t, uint64_t>(pair_add, _x0, _x1);
}

uint64_t Currying::uncurried_add3(
    const Currying::pair<uint64_t, Currying::pair<uint64_t, uint64_t>> &p) {
  const auto &[a0, a1] = p;
  const auto &[a00, a10] = a1;
  return add3(a0, a00, a10);
}

uint64_t Currying::sub(uint64_t _x0, uint64_t _x1) {
  return (((_x0 - _x1) > _x0 ? 0 : (_x0 - _x1)));
}

uint64_t Currying::flipped_sub(uint64_t _x0, uint64_t _x1) {
  return flip<uint64_t, uint64_t, uint64_t>(sub, _x0, _x1);
}

uint64_t Currying::add_base(uint64_t _x0, uint64_t _x1) { return (_x0 + _x1); }

uint64_t Currying::add_ten(uint64_t _x0) {
  return add_base((UINT64_C(2) * UINT64_C(5)), _x0);
}
