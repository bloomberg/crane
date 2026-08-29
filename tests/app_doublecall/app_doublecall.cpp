#include "app_doublecall.h"

std::deque<uint64_t> AppDoublecall::gen_list(uint64_t n) {
  if (n <= 0) {
    return std::deque<uint64_t>{};
  } else {
    uint64_t m = n - 1;
    return [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(n, gen_list(m));
  }
}

std::deque<uint64_t> AppDoublecall::concat_two(uint64_t a, uint64_t b) {
  return [&]() {
    auto _r = gen_list(a);
    auto _s = gen_list(b);
    _r.insert(_r.end(), _s.begin(), _s.end());
    return _r;
  }();
}
