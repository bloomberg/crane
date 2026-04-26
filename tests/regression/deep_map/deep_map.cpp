#include <deep_map.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Build a maximally-unbalanced tree (right spine = linked list).
/// Tail-recursive via accumulator, should be loopified.
__attribute__((pure)) DeepMap::tree<unsigned int>
DeepMap::build_right(unsigned int n, DeepMap::tree<unsigned int> acc) {
  DeepMap::tree<unsigned int> _result;
  DeepMap::tree<unsigned int> _loop_acc = std::move(acc);
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      _result = _loop_acc;
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      DeepMap::tree<unsigned int> _next_acc = tree<unsigned int>::node(
          tree<unsigned int>::leaf(), _loop_n, _loop_acc);
      unsigned int _next_n = n_;
      _loop_acc = std::move(_next_acc);
      _loop_n = std::move(_next_n);
    }
  }
  return _result;
}

__attribute__((pure)) DeepMap::tree<unsigned int>
DeepMap::map_inc(const DeepMap::tree<unsigned int> &t) {
  return tmap<unsigned int, unsigned int>(
      [](const unsigned int &x) { return (x + 1u); }, t);
}

/// Get root value.
__attribute__((pure)) unsigned int
DeepMap::root_or_zero(const DeepMap::tree<unsigned int> &t) {
  if (std::holds_alternative<typename DeepMap::tree<unsigned int>::Leaf>(
          t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename DeepMap::tree<unsigned int>::Node>(t.v());
    return d_a1;
  }
}
