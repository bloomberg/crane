#include "loopify_pair_option_child.h"

uint64_t LoopifyPairOptionChild::sum(const LoopifyPairOptionChild::tree &t) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    LoopifyPairOptionChild::tree t;
  };

  struct _after_sum_in_Some {
    uint64_t x;
    uint64_t _tmp2;
  };

  struct _after_sum_in_pair {
    uint64_t x;
    std::optional<LoopifyPairOptionChild::tree> o;
  };

  using _frame = std::variant<_call, _after_sum_in_Some, _after_sum_in_pair>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyPairOptionChild::tree &t = _f.t;
      if (std::holds_alternative<typename LoopifyPairOptionChild::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairOptionChild::tree::Node>(t.v());
        const auto &[x, o] = (*a1);
        _stack.emplace_back(_after_sum_in_pair{x, o});
        _stack.emplace_back(_call{*a0});
      }
    } else if (std::holds_alternative<_after_sum_in_Some>(_popped)) {
      auto _f = std::move(std::get<_after_sum_in_Some>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      _result = ((_f._tmp2 + x) + std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_sum_in_pair>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      std::optional<LoopifyPairOptionChild::tree> o = std::move(_f.o);
      uint64_t _tmp2 = std::move(_result);
      uint64_t _tmp1;
      if (o.has_value()) {
        const LoopifyPairOptionChild::tree &u = *o;
        _stack.emplace_back(_after_sum_in_Some{x, _tmp2});
        _stack.emplace_back(_call{u});
      } else {
        _tmp1 = UINT64_C(0);
        {
          _result = ((_tmp2 + x) + _tmp1);
        }
      }
    }
  }
  return _result;
}
