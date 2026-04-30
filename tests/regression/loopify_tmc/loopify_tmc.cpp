#include <loopify_tmc.h>

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
/// range lo hi creates lo, lo+1, ..., hi-1.
LoopifyTmc::list<unsigned int> LoopifyTmc::range(const unsigned int &lo,
                                                 const unsigned int &hi) {
  std::unique_ptr<LoopifyTmc::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyTmc::list<unsigned int>> *_write = &_head;
  unsigned int _loop_hi = hi;
  while (true) {
    if (_loop_hi <= 0) {
      *(_write) = std::make_unique<LoopifyTmc::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int hi_ = _loop_hi - 1;
      if (lo <= hi_) {
        auto _cell = std::make_unique<LoopifyTmc::list<unsigned int>>(
            typename list<unsigned int>::Cons(hi_, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_hi = hi_;
        continue;
      } else {
        *(_write) = std::make_unique<LoopifyTmc::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      }
    }
  }
  return std::move(*(_head));
}

/// prefix_sums acc l computes running prefix sums.
LoopifyTmc::list<unsigned int>
LoopifyTmc::prefix_sums(const unsigned int &acc,
                        const LoopifyTmc::list<unsigned int> &l) {
  std::unique_ptr<LoopifyTmc::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyTmc::list<unsigned int>> *_write = &_head;
  const LoopifyTmc::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename LoopifyTmc::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) = std::make_unique<LoopifyTmc::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyTmc::list<unsigned int>::Cons>(_loop_l->v());
      unsigned int s = (_loop_acc + d_a0);
      auto _cell = std::make_unique<LoopifyTmc::list<unsigned int>>(
          typename list<unsigned int>::Cons(s, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      const LoopifyTmc::list<unsigned int> *_next_l = d_a1.get();
      unsigned int _next_acc = s;
      _loop_l = _next_l;
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return std::move(*(_head));
}
