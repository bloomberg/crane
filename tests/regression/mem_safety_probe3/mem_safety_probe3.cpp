#include "mem_safety_probe3.h"

/// TEST 10: Large tree with deep recursion — stresses the
/// loopified tree traversal and clone mechanisms.
MemSafetyProbe3::tree MemSafetyProbe3::build_deep(unsigned int n) {
  std::unique_ptr<MemSafetyProbe3::tree> _head{};
  std::unique_ptr<MemSafetyProbe3::tree> *_write = &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<MemSafetyProbe3::tree>(tree::leaf());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<MemSafetyProbe3::tree>(typename tree::Node(
          nullptr, _loop_n,
          std::make_unique<MemSafetyProbe3::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write = &std::get<typename tree::Node>((*_write)->v_mut()).d_a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}
