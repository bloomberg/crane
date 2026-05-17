#include "loopify_itree_seq.h"

/// Tail-recursive countdown using erased ITree. In sequential mode, itree is
/// erased so this becomes a plain tail-recursive C++ function. Loopify should
/// convert it to a while loop.
uint64_t LoopifyItreeSeq::count_down(uint64_t n) {
  auto go_impl = [](auto &_self_go, uint64_t k, uint64_t acc) -> uint64_t {
    if (k <= 0) {
      return acc;
    } else {
      uint64_t k_ = k - 1;
      return _self_go(_self_go, k_, (acc + UINT64_C(1)));
    }
  };
  auto go = [&](uint64_t k, uint64_t acc) -> uint64_t {
    return go_impl(go_impl, k, acc);
  };
  return go(n, UINT64_C(0));
}

/// Sum 1..n via tail recursion with accumulator.
uint64_t LoopifyItreeSeq::sum_to(uint64_t n) {
  auto go_impl = [](auto &_self_go, uint64_t k, uint64_t acc) -> uint64_t {
    if (k <= 0) {
      return acc;
    } else {
      uint64_t k_ = k - 1;
      return _self_go(_self_go, k_, (acc + k));
    }
  };
  auto go = [&](uint64_t k, uint64_t acc) -> uint64_t {
    return go_impl(go_impl, k, acc);
  };
  return go(n, UINT64_C(0));
}

/// Non-tail recursive: build a list counting down from n.
List<uint64_t> LoopifyItreeSeq::countdown_list(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified countdown_list: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil());
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t n = _f.n;
      List<uint64_t> rest = _result;
      _result = List<uint64_t>::cons(n, rest);
    }
  }
  return _result;
}

uint64_t LoopifyItreeSeq::delay_ret(uint64_t n, uint64_t v) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return v;
    } else {
      uint64_t n_ = _loop_n - 1;
      _loop_n = n_;
    }
  }
}

void LoopifyItreeSeq::spin() {
  while (true) {
  }
  return;
}

void LoopifyItreeSeq::forever(uint64_t n) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    _loop_n = (_loop_n + 1);
  }
  return;
}

uint64_t LoopifyItreeSeq::test_count_5() { return count_down(UINT64_C(5)); }

uint64_t LoopifyItreeSeq::test_sum_10() { return sum_to(UINT64_C(10)); }

List<uint64_t> LoopifyItreeSeq::test_clist_4() {
  return countdown_list(UINT64_C(4));
}

uint64_t LoopifyItreeSeq::test_delay() {
  return delay_ret(UINT64_C(5), UINT64_C(42));
}
