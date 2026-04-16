#include <loopify_tail.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Tail-recursive: membership test
__attribute__((pure)) bool
LoopifyTail::member(const unsigned int x,
                    const std::shared_ptr<LoopifyTail::list<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<LoopifyTail::list<unsigned int>> _loop_l = l;
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
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

/// Tail-recursive: nth element
__attribute__((pure)) unsigned int
LoopifyTail::nth(const unsigned int n,
                 const std::shared_ptr<LoopifyTail::list<unsigned int>> &l,
                 const unsigned int default0) {
  unsigned int _result;
  std::shared_ptr<LoopifyTail::list<unsigned int>> _loop_l = l;
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
        std::shared_ptr<LoopifyTail::list<unsigned int>> _next_l = d_a1;
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

/// Tail-recursive: lookup in association list
__attribute__((pure)) unsigned int LoopifyTail::lookup(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyTail::list<std::pair<unsigned int, unsigned int>>> &l) {
  unsigned int _result;
  std::shared_ptr<LoopifyTail::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
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
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}
