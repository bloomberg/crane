#include "mutual_loopify_acc.h"

uint64_t MutualLoopifyAcc::tsum(uint64_t acc, const MutualLoopifyAcc::tree &t) {
  // Explicit stack replaces the non-tail recursion of tsum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MutualLoopifyAcc::tree *t;
  };

  struct _after_tsum_in_Fcons {
    std::shared_ptr<MutualLoopifyAcc::forest> a10;
  };

  using _frame = std::variant<_call, _after_tsum_in_Fcons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MutualLoopifyAcc::tree &t = *_f.t;
      if (std::holds_alternative<typename MutualLoopifyAcc::tree::Leaf>(t.v())) {
        const auto &[a0] =
            std::get<typename MutualLoopifyAcc::tree::Leaf>(t.v());
        _result = (acc + a0);
      } else {
        const auto &[a0] =
            std::get<typename MutualLoopifyAcc::tree::Node>(t.v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
                _sv0.v())) {
          _result = acc;
        } else {
          const auto &[a00, a10] =
              std::get<typename MutualLoopifyAcc::forest::Fcons>(_sv0.v());
          _stack.emplace_back(_after_tsum_in_Fcons{a10});
          _stack.emplace_back(_call{crane_raw(a00)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_tsum_in_Fcons>(_popped));
      std::shared_ptr<MutualLoopifyAcc::forest> a10 = std::move(_f.a10);
      _result = fsum(std::move(_result), *a10);
    }
  }
  return _result;
}

uint64_t MutualLoopifyAcc::fsum(uint64_t acc,
                                const MutualLoopifyAcc::forest &f) {
  // Explicit stack replaces the non-tail recursion of fsum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MutualLoopifyAcc::forest *f;
    uint64_t acc;
  };

  struct _call_tsum_entry {
    const MutualLoopifyAcc::tree *t;
    uint64_t acc0;
  };

  struct _after_tsum_entry_in_Fcons {
    const MutualLoopifyAcc::forest *a10;
  };

  using _frame =
      std::variant<_call, _call_tsum_entry, _after_tsum_entry_in_Fcons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&f, acc});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MutualLoopifyAcc::forest &f = *_f.f;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(f.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a00, a10] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(f.v());
        _stack.emplace_back(_after_tsum_entry_in_Fcons{crane_raw(a10)});
        _stack.emplace_back(_call_tsum_entry{crane_raw(a00), acc});
      }
    } else if (std::holds_alternative<_call_tsum_entry>(_popped)) {
      auto _f = std::move(std::get<_call_tsum_entry>(_popped));
      const MutualLoopifyAcc::tree &t = *_f.t;
      uint64_t acc0 = _f.acc0;
      if (std::holds_alternative<typename MutualLoopifyAcc::tree::Leaf>(t.v())) {
        const auto &[a0] =
            std::get<typename MutualLoopifyAcc::tree::Leaf>(t.v());
        _result = (acc0 + a0);
      } else {
        const auto &[a0] =
            std::get<typename MutualLoopifyAcc::tree::Node>(t.v());
        _stack.emplace_back(_call{crane_raw(a0), acc0});
      }
    } else {
      auto _f = std::move(std::get<_after_tsum_entry_in_Fcons>(_popped));
      const MutualLoopifyAcc::forest &a10 = *_f.a10;
      _stack.emplace_back(_call{&a10, std::move(_result)});
    }
  }
  return _result;
}

MutualLoopifyAcc::tree MutualLoopifyAcc::chain(uint64_t n,
                                               MutualLoopifyAcc::tree acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MutualLoopifyAcc::tree _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      _loop_acc =
          tree::node(forest::fcons(
              std::move(_loop_acc),
              forest::fcons(tree::leaf(UINT64_C(1)), forest::fnil())));
      _loop_n = m;
    }
  }
}

uint64_t MutualLoopifyAcc::go(uint64_t n) {
  return tsum(UINT64_C(0), chain(n, tree::leaf(UINT64_C(0))));
}
