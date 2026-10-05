#include "loopify_tmc.h"

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
/// range lo hi creates lo, lo+1, ..., hi-1.
LoopifyTmc::list<uint64_t> LoopifyTmc::range(uint64_t lo, uint64_t hi) {
  std::optional<LoopifyTmc::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyTmc::list<uint64_t>> *_write = nullptr;
  uint64_t _loop_hi = std::move(hi);
  while (true) {
    if (_loop_hi <= 0) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyTmc::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t hi_ = _loop_hi - 1;
      if (lo <= hi_) {
        auto _cell = typename LoopifyTmc::list<uint64_t>::Cons(hi_, nullptr);
        LoopifyTmc::list<uint64_t> &_node =
            (_write ? *(*_write = std::make_shared<LoopifyTmc::list<uint64_t>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyTmc::list<uint64_t>::Cons>(_node.v_mut())
                 .l;
        _loop_hi = hi_;
        continue;
      } else {
        auto _value = list<uint64_t>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyTmc::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      }
    }
  }
  return std::move(*_root);
}

/// prefix_sums acc l computes running prefix sums.
LoopifyTmc::list<uint64_t>
LoopifyTmc::prefix_sums(uint64_t acc, const LoopifyTmc::list<uint64_t> &l) {
  std::optional<LoopifyTmc::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyTmc::list<uint64_t>> *_write = nullptr;
  const LoopifyTmc::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyTmc::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyTmc::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyTmc::list<uint64_t>::Cons>(_loop_l->v());
      uint64_t s = (_loop_acc + a0);
      auto _cell = typename LoopifyTmc::list<uint64_t>::Cons(s, nullptr);
      LoopifyTmc::list<uint64_t> &_node =
          (_write ? *(*_write = std::make_shared<LoopifyTmc::list<uint64_t>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyTmc::list<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      _loop_acc = s;
      continue;
    }
  }
  return std::move(*_root);
}
