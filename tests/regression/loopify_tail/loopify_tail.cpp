#include "loopify_tail.h"

/// Tail-recursive: membership test
bool LoopifyTail::member(uint64_t x, const LoopifyTail::list<uint64_t> &l) {
  const LoopifyTail::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyTail::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return true;
      } else {
        _loop_l = a1.get();
      }
    }
  }
} /// Tail-recursive: nth element

uint64_t LoopifyTail::nth(uint64_t n, const LoopifyTail::list<uint64_t> &l,
                          uint64_t default0) {
  const LoopifyTail::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyTail::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return a0;
      } else {
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

/// Tail-recursive: lookup in association list
uint64_t
LoopifyTail::lookup(uint64_t key,
                    const LoopifyTail::list<std::pair<uint64_t, uint64_t>> &l) {
  const LoopifyTail::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyTail::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyTail::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      if (a0.first == key) {
        return a0.second;
      } else {
        _loop_l = a1.get();
      }
    }
  }
}
