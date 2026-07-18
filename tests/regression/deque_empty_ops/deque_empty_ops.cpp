#include "deque_empty_ops.h"

uint64_t DequeEmptyOps::double_(uint64_t n) { return (n * UINT64_C(2)); }

std::deque<uint64_t> DequeEmptyOps::dup(uint64_t n) {
  return [](auto _a0, auto _a1) {
    _a1.push_front(_a0);
    return _a1;
  }(n, [](auto _a0, auto _a1) {
    _a1.push_front(_a0);
    return _a1;
  }(n, std::deque<uint64_t>{}));
}

std::deque<uint64_t> DequeEmptyOps::run_map(const std::deque<uint64_t> &l) {
  return [&]() {
    std::deque<std::decay_t<decltype(double_(
        std::declval<typename std::decay_t<decltype(l)>::value_type &>()))>>
        _r;
    for (const auto &_x : l)
      _r.push_back(double_(_x));
    return _r;
  }();
}

std::deque<uint64_t> DequeEmptyOps::run_flatmap(const std::deque<uint64_t> &l) {
  return [&]() {
    std::deque<typename std::decay_t<decltype(dup(
        std::declval<typename std::decay_t<decltype(l)>::value_type &>()))>::
                   value_type>
        _r;
    for (const auto &_x : l) {
      auto _s = dup(_x);
      _r.insert(_r.end(), _s.begin(), _s.end());
    }
    return _r;
  }();
}

std::deque<uint64_t>
DequeEmptyOps::run_concat(const std::deque<std::deque<uint64_t>> &_x0) {
  return [&]() {
    std::deque<typename std::decay_t<decltype(_x0)>::value_type::value_type> _r;
    for (const auto &_s : _x0)
      _r.insert(_r.end(), _s.begin(), _s.end());
    return _r;
  }();
}
