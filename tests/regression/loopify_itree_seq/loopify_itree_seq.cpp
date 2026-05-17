#include "loopify_itree_seq.h"

/// Tail-recursive countdown using erased ITree. In sequential mode, itree is
/// erased so this becomes a plain tail-recursive C++ function. Loopify should
/// convert it to a while loop.
unsigned int LoopifyItreeSeq::count_down(unsigned int n) {
  auto go_impl = [](auto &_self_go, unsigned int k,
                    unsigned int acc) -> unsigned int {
    if (k <= 0) {
      return acc;
    } else {
      unsigned int k_ = k - 1;
      return _self_go(_self_go, k_, (acc + 1u));
    }
  };
  auto go = [&](unsigned int k, unsigned int acc) -> unsigned int {
    return go_impl(go_impl, k, acc);
  };
  return go(n, 0u);
}

/// Sum 1..n via tail recursion with accumulator.
unsigned int LoopifyItreeSeq::sum_to(unsigned int n) {
  auto go_impl = [](auto &_self_go, unsigned int k,
                    unsigned int acc) -> unsigned int {
    if (k <= 0) {
      return acc;
    } else {
      unsigned int k_ = k - 1;
      return _self_go(_self_go, k_, (acc + k));
    }
  };
  auto go = [&](unsigned int k, unsigned int acc) -> unsigned int {
    return go_impl(go_impl, k, acc);
  };
  return go(n, 0u);
}

/// Non-tail recursive: build a list counting down from n.
List<unsigned int> LoopifyItreeSeq::countdown_list(
    unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Cont_n_: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified countdown_list: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::cons(0u, List<unsigned int>::nil());
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      unsigned int n = _f.n;
      List<unsigned int> rest = _result;
      _result = List<unsigned int>::cons(n, rest);
    }
  }
  return _result;
}

unsigned int LoopifyItreeSeq::delay_ret(unsigned int n, unsigned int v) {
  unsigned int _result;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      _result = std::move(v);
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      _loop_n = n_;
    }
  }
  return _result;
}

void LoopifyItreeSeq::spin() {
  while (true) {
  }
  return;
}

void LoopifyItreeSeq::forever(unsigned int n) {
  unsigned int _loop_n = std::move(n);
  while (true) {
    _loop_n = (_loop_n + 1);
  }
  return;
}

unsigned int LoopifyItreeSeq::test_count_5() { return count_down(5u); }

unsigned int LoopifyItreeSeq::test_sum_10() { return sum_to(10u); }

List<unsigned int> LoopifyItreeSeq::test_clist_4() {
  return countdown_list(4u);
}

unsigned int LoopifyItreeSeq::test_delay() { return delay_ret(5u, 42u); }
