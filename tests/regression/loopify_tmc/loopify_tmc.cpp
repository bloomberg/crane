#include <loopify_tmc.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
/// range lo hi creates lo, lo+1, ..., hi-1.
std::shared_ptr<LoopifyTmc::list<unsigned int>>
LoopifyTmc::range(const unsigned int lo, const unsigned int hi) {
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _last{};
  unsigned int _loop_hi = hi;
  bool _continue = true;
  while (_continue) {
    if (_loop_hi <= 0) {
      {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              list<unsigned int>::nil();
        } else {
          _head = list<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int hi_ = _loop_hi - 1;
      if (lo <= hi_) {
        {
          auto _cell = list<unsigned int>::cons(hi_, nullptr);
          if (_last) {
            std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_hi = hi_;
          continue;
        }
      } else {
        {
          if (_last) {
            std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                list<unsigned int>::nil();
          } else {
            _head = list<unsigned int>::nil();
          }
          _continue = false;
        }
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
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyTmc::list<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyTmc::list<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyTmc::list<unsigned int>::Cons _args) {
              unsigned int s = (_loop_acc + _args.d_a0);
              auto _cell = list<unsigned int>::cons(s, nullptr);
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<LoopifyTmc::list<unsigned int>> _next_l =
                  _args.d_a1;
              unsigned int _next_acc = s;
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _head;
}
