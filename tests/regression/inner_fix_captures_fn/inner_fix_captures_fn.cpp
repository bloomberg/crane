#include "inner_fix_captures_fn.h"

InnerFixCapturesFn::lst InnerFixCapturesFn::mk(uint64_t n) {
  std::optional<InnerFixCapturesFn::lst> _root{};
  std::shared_ptr<InnerFixCapturesFn::lst> *_write = nullptr;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      auto _value = lst::nil();
      (_write ? *(*_write = std::make_shared<InnerFixCapturesFn::lst>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = typename InnerFixCapturesFn::lst::Cons(UINT64_C(1), nullptr);
      InnerFixCapturesFn::lst &_node =
          (_write ? *(*_write = std::make_shared<InnerFixCapturesFn::lst>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename InnerFixCapturesFn::lst::Cons>(_node.v_mut()).a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t InnerFixCapturesFn::go(uint64_t n) {
  return walk([](uint64_t k) { return (k + UINT64_C(1)); }, mk(n));
}
