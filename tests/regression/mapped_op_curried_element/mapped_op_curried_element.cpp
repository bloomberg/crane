#include "mapped_op_curried_element.h"

uint64_t MappedOpCurriedElement::deque_map(
    const std::deque<crane::fn<uint64_t(uint64_t, uint64_t)>> &l) {
  return static_cast<uint64_t>(([](auto _f, const auto &_l) {
    std::deque<crane::fn<uint64_t(uint64_t, uint64_t)>> _r;
    for (const auto &_x : _l) _r.push_back(_f(_x));
    return _r;
  }([](crane::fn<uint64_t(uint64_t, uint64_t)> g) { return g; }, l)).size());
}

uint64_t MappedOpCurriedElement::maybe_get(
    const std::optional<crane::fn<uint64_t(uint64_t, uint64_t)>> &m) {
  return [](const auto &_m, auto _d) { return _m.has_value() ? *_m : _d; }(
      m, crane::fn<uint64_t(uint64_t, uint64_t)>(
             [](uint64_t x, uint64_t) { return x; }))(UINT64_C(1), UINT64_C(2));
}
