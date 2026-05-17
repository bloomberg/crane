#include "loopify_tail.h"

/// Tail-recursive: membership test
bool LoopifyTail::member(unsigned int x,
                         const LoopifyTail::list<unsigned int> &l) {
  bool _result;
  const LoopifyTail::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyTail::list<unsigned int>::Cons>(
              _loop_l->v());
      if (x == a0) {
        _result = true;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

/// Tail-recursive: nth element
unsigned int LoopifyTail::nth(unsigned int n,
                              const LoopifyTail::list<unsigned int> &l,
                              unsigned int default0) {
  unsigned int _result;
  const LoopifyTail::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = default0;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyTail::list<unsigned int>::Cons>(
              _loop_l->v());
      if (_loop_n == 0u) {
        _result = a0;
        break;
      } else {
        _loop_l = a1.get();
        _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      }
    }
  }
  return _result;
}

/// Tail-recursive: lookup in association list
unsigned int LoopifyTail::lookup(
    unsigned int key,
    const LoopifyTail::list<std::pair<unsigned int, unsigned int>> &l) {
  unsigned int _result;
  const LoopifyTail::list<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[a0, a1] = std::get<typename LoopifyTail::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l->v());
      if (a0.first == key) {
        _result = a0.second;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}
