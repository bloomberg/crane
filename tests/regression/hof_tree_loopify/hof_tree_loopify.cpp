#include "hof_tree_loopify.h"

HofTreeLoopify::tree<uint64_t> HofTreeLoopify::depth_tree(uint64_t n) {
  std::optional<HofTreeLoopify::tree<uint64_t>> _root{};
  std::shared_ptr<HofTreeLoopify::tree<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree<uint64_t>::leaf();
      (_write ? *(*_write = std::make_shared<HofTreeLoopify::tree<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = typename HofTreeLoopify::tree<uint64_t>::Node(
          nullptr, _loop_n,
          std::make_shared<HofTreeLoopify::tree<uint64_t>>(
              tree<uint64_t>::leaf()));
      HofTreeLoopify::tree<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<HofTreeLoopify::tree<uint64_t>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename HofTreeLoopify::tree<uint64_t>::Node>(
                    _node.v_mut())
                    .l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}
