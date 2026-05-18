#include "deep_map.h"

/// Build a maximally-unbalanced tree (right spine = linked list).
/// Tail-recursive via accumulator, should be loopified.
DeepMap::tree<uint64_t> DeepMap::build_right(uint64_t n,
                                             DeepMap::tree<uint64_t> acc) {
  DeepMap::tree<uint64_t> _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_acc = tree<uint64_t>::node(tree<uint64_t>::leaf(), _loop_n,
                                       std::move(_loop_acc));
      _loop_n = _next_n;
    }
  }
}

DeepMap::tree<uint64_t> DeepMap::map_inc(const DeepMap::tree<uint64_t> &t) {
  return tmap<uint64_t, uint64_t>([](uint64_t x) { return (x + UINT64_C(1)); },
                                  t);
}

/// Get root value.
uint64_t DeepMap::root_or_zero(const DeepMap::tree<uint64_t> &t) {
  if (std::holds_alternative<typename DeepMap::tree<uint64_t>::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename DeepMap::tree<uint64_t>::Node>(t.v());
    return a1;
  }
}
