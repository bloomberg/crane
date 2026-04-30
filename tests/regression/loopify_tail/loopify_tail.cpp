#include <loopify_tail.h>

/// Tail-recursive: membership test
bool LoopifyTail::member(const unsigned int &x,
                         const LoopifyTail::list<unsigned int> &l) {
  bool _result;
  const LoopifyTail::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyTail::list<unsigned int>::Cons>(
              _loop_l->v());
      if (x == d_a0) {
        _result = true;
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}

/// Tail-recursive: nth element
unsigned int LoopifyTail::nth(const unsigned int &n,
                              const LoopifyTail::list<unsigned int> &l,
                              unsigned int default0) {
  unsigned int _result;
  const LoopifyTail::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = default0;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyTail::list<unsigned int>::Cons>(
              _loop_l->v());
      if (_loop_n == 0u) {
        _result = d_a0;
        break;
      } else {
        const LoopifyTail::list<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = _next_l;
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

/// Tail-recursive: lookup in association list
unsigned int LoopifyTail::lookup(
    const unsigned int &key,
    const LoopifyTail::list<std::pair<unsigned int, unsigned int>> &l) {
  unsigned int _result;
  const LoopifyTail::list<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyTail::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename LoopifyTail::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l->v());
      if (d_a0.first == key) {
        _result = d_a0.second;
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}
