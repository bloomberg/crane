#include "loopify_itree_seq.h"

/// Tail-recursive countdown using erased ITree. In sequential mode, itree is
/// erased so this becomes a plain tail-recursive C++ function. Loopify should
/// convert it to a while loop.
uint64_t LoopifyItreeSeq::count_down(uint64_t n) {
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_acc = _lc1_acc;
  while (true) {
    if (n <= 0) {
      return _lc1_loop_acc;
    } else {
      uint64_t k_ = n - 1;
      _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
      n = k_;
    }
  }
}

/// Sum 1..n via tail recursion with accumulator.
uint64_t LoopifyItreeSeq::sum_to(uint64_t n) {
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_acc = _lc1_acc;
  while (true) {
    if (n <= 0) {
      return _lc1_loop_acc;
    } else {
      uint64_t k_ = n - 1;
      uint64_t _next_k = k_;
      _lc1_loop_acc = (_lc1_loop_acc + n);
      n = _next_k;
    }
  }
}

/// Non-tail recursive: build a list counting down from n.
List<uint64_t> LoopifyItreeSeq::countdown_list(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of countdown_list: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_countdown_list_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_countdown_list_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil());
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_countdown_list_in_S{n});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_countdown_list_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(n, std::move(rest));
    }
  }
  return _result;
}

uint64_t LoopifyItreeSeq::delay_ret(uint64_t n, uint64_t v) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return v;
    } else {
      uint64_t n_ = n - 1;
      n = n_;
    }
  }
}

void LoopifyItreeSeq::spin() {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
  }
}

void LoopifyItreeSeq::forever(uint64_t) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
  }
}

uint64_t LoopifyItreeSeq::test_count_5() { return count_down(UINT64_C(5)); }

uint64_t LoopifyItreeSeq::test_sum_10() { return sum_to(UINT64_C(10)); }

List<uint64_t> LoopifyItreeSeq::test_clist_4() {
  return countdown_list(UINT64_C(4));
}

uint64_t LoopifyItreeSeq::test_delay() {
  return delay_ret(UINT64_C(5), UINT64_C(42));
}
