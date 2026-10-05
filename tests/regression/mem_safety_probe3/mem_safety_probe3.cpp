#include "mem_safety_probe3.h"

/// TEST 10: Large tree with deep recursion — stresses the
/// loopified tree traversal and clone mechanisms.
MemSafetyProbe3::tree MemSafetyProbe3::build_deep(uint64_t n) {
  std::optional<MemSafetyProbe3::tree> _root{};
  std::shared_ptr<MemSafetyProbe3::tree> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe3::tree>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename MemSafetyProbe3::tree::Node(
          nullptr, _loop_n,
          std::make_shared<MemSafetyProbe3::tree>(tree::leaf()));
      MemSafetyProbe3::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe3::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe3::tree::Node>(_node.v_mut()).a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}
