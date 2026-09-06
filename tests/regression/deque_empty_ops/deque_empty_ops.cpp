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
  return [](auto _f, const auto &_l) {
    std::deque<std::decay_t<decltype(_f(
        std::declval<typename std::decay_t<decltype(_l)>::value_type &>()))>>
        _r;
    for (const auto &_x : _l)
      _r.push_back(_f(_x));
    return _r;
  }(double_, l);
}

std::deque<uint64_t> DequeEmptyOps::run_flatmap(const std::deque<uint64_t> &l) {
  return [](auto _f, const auto &_l) {
    std::deque<typename std::decay_t<decltype(_f(
        std::declval<typename std::decay_t<decltype(_l)>::value_type &>()))>::
                   value_type>
        _r;
    for (const auto &_x : _l) {
      auto _s = _f(_x);
      _r.insert(_r.end(), _s.begin(), _s.end());
    }
    return _r;
  }(dup, l);
}

std::deque<uint64_t>
DequeEmptyOps::run_concat(const std::deque<std::deque<uint64_t>> &x0_) {
  return [](const auto &_ls) {
    std::deque<typename std::decay_t<decltype(_ls)>::value_type::value_type> _r;
    for (const auto &_s : _ls)
      _r.insert(_r.end(), _s.begin(), _s.end());
    return _r;
  }(x0_);
}
