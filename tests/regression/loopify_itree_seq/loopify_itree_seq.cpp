#include <loopify_itree_seq.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Tail-recursive countdown using erased ITree. In sequential mode, itree is
/// erased so this becomes a plain tail-recursive C++ function. Loopify should
/// convert it to a while loop.
unsigned int LoopifyItreeSeq::count_down(const unsigned int n) {
  std::function<unsigned int(unsigned int, unsigned int)> go;
  go = [](unsigned int k, unsigned int acc) -> unsigned int {
    unsigned int _result;
    unsigned int _loop_acc = acc;
    unsigned int _loop_k = k;
    bool _continue = true;
    while (_continue) {
      if (_loop_k <= 0) {
        {
          _result = _loop_acc;
          _continue = false;
        }
      } else {
        unsigned int k_ = _loop_k - 1;
        {
          unsigned int _next_acc = (_loop_acc + 1u);
          unsigned int _next_k = k_;
          _loop_acc = std::move(_next_acc);
          _loop_k = std::move(_next_k);
        }
      }
    }
    return _result;
  };
  return go(n, 0u);
}

/// Sum 1..n via tail recursion with accumulator.
unsigned int LoopifyItreeSeq::sum_to(const unsigned int n) {
  std::function<unsigned int(unsigned int, unsigned int)> go;
  go = [](unsigned int k, unsigned int acc) -> unsigned int {
    unsigned int _result;
    unsigned int _loop_acc = acc;
    unsigned int _loop_k = k;
    bool _continue = true;
    while (_continue) {
      if (_loop_k <= 0) {
        {
          _result = _loop_acc;
          _continue = false;
        }
      } else {
        unsigned int k_ = _loop_k - 1;
        {
          unsigned int _next_acc = (_loop_acc + _loop_k);
          unsigned int _next_k = k_;
          _loop_acc = std::move(_next_acc);
          _loop_k = std::move(_next_k);
        }
      }
    }
    return _result;
  };
  return go(n, 0u);
}

/// Non-tail recursive: build a list counting down from n.
std::shared_ptr<List<unsigned int>>
LoopifyItreeSeq::countdown_list(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::cons(
                                  0u, List<unsigned int>::nil());
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.emplace_back(_Call1{n});
                              _stack.emplace_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) {
                            const unsigned int n = _f._s0;
                            std::shared_ptr<List<unsigned int>> rest = _result;
                            _result = List<unsigned int>::cons(n, rest);
                          }},
               _frame);
  }
  return _result;
}

unsigned int LoopifyItreeSeq::delay_ret(const unsigned int n,
                                        const unsigned int v) {
  unsigned int _result;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = v;
        _continue = false;
      }
    } else {
      unsigned int n_ = _loop_n - 1;
      {
        _loop_n = n_;
      }
    }
  }
  return _result;
}

void LoopifyItreeSeq::spin() {
  while (true) {
  }
  return;
}

void LoopifyItreeSeq::forever(const unsigned int n) {
  unsigned int _loop_n = n;
  while (true) {
    {
      _loop_n = (_loop_n + 1);
    }
  }
  return;
}

unsigned int LoopifyItreeSeq::test_count_5() { return count_down(5u); }

unsigned int LoopifyItreeSeq::test_sum_10() { return sum_to(10u); }

std::shared_ptr<List<unsigned int>> LoopifyItreeSeq::test_clist_4() {
  return countdown_list(4u);
}

unsigned int LoopifyItreeSeq::test_delay() { return delay_ret(5u, 42u); }
