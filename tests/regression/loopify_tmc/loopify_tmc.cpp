#include "loopify_tmc.h"

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
/// range lo hi creates lo, lo+1, ..., hi-1.
LoopifyTmc::list<uint64_t> LoopifyTmc::range(uint64_t lo, uint64_t hi) {
  std::shared_ptr<LoopifyTmc::list<uint64_t>> _head{};
  std::shared_ptr<LoopifyTmc::list<uint64_t>> *_write = &_head;
  uint64_t _loop_hi = std::move(hi);
  while (true) {
    if (_loop_hi <= 0) {
      *_write =
          std::make_shared<LoopifyTmc::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      uint64_t hi_ = _loop_hi - 1;
      if (lo <= hi_) {
        auto _cell = std::make_shared<LoopifyTmc::list<uint64_t>>(
            typename list<uint64_t>::Cons(hi_, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_hi = hi_;
        continue;
      } else {
        *_write =
            std::make_shared<LoopifyTmc::list<uint64_t>>(list<uint64_t>::nil());
        break;
      }
    }
  }
  return std::move(*_head);
}

/// prefix_sums acc l computes running prefix sums.
LoopifyTmc::list<uint64_t>
LoopifyTmc::prefix_sums(uint64_t acc, const LoopifyTmc::list<uint64_t> &l) {
  std::shared_ptr<LoopifyTmc::list<uint64_t>> _head{};
  std::shared_ptr<LoopifyTmc::list<uint64_t>> *_write = &_head;
  const LoopifyTmc::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyTmc::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_shared<LoopifyTmc::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyTmc::list<uint64_t>::Cons>(_loop_l->v());
      uint64_t s = (_loop_acc + a0);
      auto _cell = std::make_shared<LoopifyTmc::list<uint64_t>>(
          typename list<uint64_t>::Cons(s, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = a1.get();
      _loop_acc = s;
      continue;
    }
  }
  return std::move(*_head);
}
