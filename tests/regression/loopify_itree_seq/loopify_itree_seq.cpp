#include "loopify_itree_seq.h"

/// Tail-recursive countdown using erased ITree. In sequential mode, itree is
/// erased so this becomes a plain tail-recursive C++ function. Loopify should
/// convert it to a while loop.
uint64_t LoopifyItreeSeq::count_down(uint64_t n) {
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    uint64_t _lc1_loop_k = std::move(_lc1_k);
    while (true) {
      if (_lc1_loop_k <= 0) {
        return _lc1_loop_acc;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
        _lc1_loop_k = k_;
      }
    }
  }
}

/// Sum 1..n via tail recursion with accumulator.
uint64_t LoopifyItreeSeq::sum_to(uint64_t n) {
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    uint64_t _lc1_loop_k = std::move(_lc1_k);
    while (true) {
      if (_lc1_loop_k <= 0) {
        return _lc1_loop_acc;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        uint64_t _next_k = k_;
        _lc1_loop_acc = (_lc1_loop_acc + _lc1_loop_k);
        _lc1_loop_k = _next_k;
      }
    }
  }
}

/// Non-tail recursive: build a list counting down from n.
List<uint64_t> LoopifyItreeSeq::countdown_list(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified countdown_list: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil());
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(n, std::move(rest));
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
