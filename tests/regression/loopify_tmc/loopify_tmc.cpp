#include <loopify_tmc.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
/// range lo hi creates lo, lo+1, ..., hi-1.
std::shared_ptr<LoopifyTmc::list<unsigned int>>
LoopifyTmc::range(const unsigned int lo, const unsigned int hi) {
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyTmc::list<unsigned int>> *_write = &_head;
  unsigned int _loop_hi = hi;
  while (true) {
    if (_loop_hi <= 0) {
      *_write = list<unsigned int>::nil();
      break;
    } else {
      unsigned int hi_ = _loop_hi - 1;
      if (lo <= hi_) {
        auto _cell = list<unsigned int>::cons(hi_, nullptr);
        *_write = _cell;
        _write =
            &std::get<typename list<unsigned int>::Cons>(_cell->v_mut()).d_a1;
        _loop_hi = hi_;
        continue;
      } else {
        *_write = list<unsigned int>::nil();
        break;
      }
    }
  }
  return _head;
}

/// prefix_sums acc l computes running prefix sums.
std::shared_ptr<LoopifyTmc::list<unsigned int>> LoopifyTmc::prefix_sums(
    const unsigned int acc,
    const std::shared_ptr<LoopifyTmc::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyTmc::list<unsigned int>> *_write = &_head;
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename LoopifyTmc::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = list<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyTmc::list<unsigned int>::Cons>(_loop_l->v());
      unsigned int s = (_loop_acc + d_a0);
      auto _cell = list<unsigned int>::cons(s, nullptr);
      *_write = _cell;
      _write =
          &std::get<typename list<unsigned int>::Cons>(_cell->v_mut()).d_a1;
      std::shared_ptr<LoopifyTmc::list<unsigned int>> _next_l = d_a1;
      unsigned int _next_acc = s;
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return _head;
}
