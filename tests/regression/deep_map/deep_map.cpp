#include <deep_map.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Build a maximally-unbalanced tree (right spine = linked list).
/// Tail-recursive via accumulator, should be loopified.
std::shared_ptr<DeepMap::tree<unsigned int>>
DeepMap::build_right(const unsigned int n,
                     std::shared_ptr<DeepMap::tree<unsigned int>> acc) {
  std::shared_ptr<DeepMap::tree<unsigned int>> _result;
  std::shared_ptr<DeepMap::tree<unsigned int>> _loop_acc = acc;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = std::move(_loop_acc);
        _continue = false;
      }
    } else {
      unsigned int n_ = _loop_n - 1;
      {
        std::shared_ptr<DeepMap::tree<unsigned int>> _next_acc =
            tree<unsigned int>::node(tree<unsigned int>::leaf(), _loop_n,
                                     _loop_acc);
        unsigned int _next_n = n_;
        _loop_acc = std::move(_next_acc);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

std::shared_ptr<DeepMap::tree<unsigned int>>
DeepMap::map_inc(const std::shared_ptr<DeepMap::tree<unsigned int>> &t) {
  return tmap<unsigned int, unsigned int>(
      [](unsigned int x) { return (x + 1u); }, t);
}

/// Get root value.
__attribute__((pure)) unsigned int
DeepMap::root_or_zero(const std::shared_ptr<DeepMap::tree<unsigned int>> &t) {
  return std::visit(
      Overloaded{[](const typename DeepMap::tree<unsigned int>::Leaf &)
                     -> unsigned int { return 0u; },
                 [](const typename DeepMap::tree<unsigned int>::Node &_args)
                     -> unsigned int { return _args.d_a1; }},
      t->v());
}
