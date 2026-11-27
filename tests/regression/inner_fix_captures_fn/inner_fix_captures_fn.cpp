#include "inner_fix_captures_fn.h"

InnerFixCapturesFn::lst InnerFixCapturesFn::mk(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<InnerFixCapturesFn::lst> _root{};
  std::shared_ptr<InnerFixCapturesFn::lst> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = lst::nil();
      (_write ? *(*_write = std::make_shared<InnerFixCapturesFn::lst>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename InnerFixCapturesFn::lst::Cons(UINT64_C(1), nullptr);
      InnerFixCapturesFn::lst &_node =
          (_write ? *(*_write = std::make_shared<InnerFixCapturesFn::lst>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename InnerFixCapturesFn::lst::Cons>(_node.v_mut()).a1;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t InnerFixCapturesFn::go(uint64_t n) {
  return walk([](uint64_t k) { return k + UINT64_C(1); }, mk(n));
}
