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
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyTail::list<unsigned int>::Nil &) {
              _result = false;
              _continue = false;
            },
            [&](const typename LoopifyTail::list<unsigned int>::Cons &_args) {
              if (x == _args.d_a0) {
                _result = true;
                _continue = false;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
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
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyTail::list<unsigned int>::Nil &) {
              _result = default0;
              _continue = false;
            },
            [&](const typename LoopifyTail::list<unsigned int>::Cons &_args) {
              if (_loop_n == 0u) {
                _result = _args.d_a0;
                _continue = false;
              } else {
                std::shared_ptr<LoopifyTail::list<unsigned int>> _next_l =
                    _args.d_a1;
                unsigned int _next_n =
                    (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }
            }},
        _loop_l->v());
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
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename LoopifyTail::list<
                       std::pair<unsigned int, unsigned int>>::Nil &) {
                     _result = 0u;
                     _continue = false;
                   },
                   [&](const typename LoopifyTail::list<
                       std::pair<unsigned int, unsigned int>>::Cons &_args) {
                     if (_args.d_a0.first == key) {
                       _result = _args.d_a0.second;
                       _continue = false;
                     } else {
                       _loop_l = _args.d_a1;
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}
