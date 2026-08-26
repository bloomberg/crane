#include "inner_fix_captures_fn.h"

InnerFixCapturesFn::lst InnerFixCapturesFn::mk(uint64_t n) {
  std::shared_ptr<InnerFixCapturesFn::lst> _head{};
  std::shared_ptr<InnerFixCapturesFn::lst> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<InnerFixCapturesFn::lst>(lst::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_shared<InnerFixCapturesFn::lst>(
          typename lst::Cons(UINT64_C(1), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename lst::Cons>((*_write)->v_mut()).a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t InnerFixCapturesFn::go(uint64_t n) {
  return walk([](uint64_t k) { return (k + UINT64_C(1)); }, mk(n));
}
