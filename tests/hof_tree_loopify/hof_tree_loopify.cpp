#include "hof_tree_loopify.h"

HofTreeLoopify::tree<uint64_t> HofTreeLoopify::depth_tree(uint64_t n) {
  std::shared_ptr<HofTreeLoopify::tree<uint64_t>> _head{};
  std::shared_ptr<HofTreeLoopify::tree<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<HofTreeLoopify::tree<uint64_t>>(
          tree<uint64_t>::leaf());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_shared<HofTreeLoopify::tree<uint64_t>>(
          typename tree<uint64_t>::Node(
              nullptr, _loop_n,
              std::make_shared<HofTreeLoopify::tree<uint64_t>>(
                  tree<uint64_t>::leaf())));
      *_write = std::move(_cell);
      _write = &std::get<typename tree<uint64_t>::Node>((*_write)->v_mut()).l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}
