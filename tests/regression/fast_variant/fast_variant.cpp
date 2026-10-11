#include "fast_variant.h"

FastVariant::tree FastVariant::build(const List<uint64_t> &l) {
  return l.template fold_right<FastVariant::tree>(
      [](const uint64_t &_x0, const FastVariant::tree &_x1) {
        return _x1.insert(_x0);
      },
      tree::leaf());
}

FastVariant::stream FastVariant::from(uint64_t n) {
  return stream::lazy_([=]() -> typename FastVariant::stream::Cons {
    return {n, from((n + 1))};
  });
}

List<uint64_t> FastVariant::take(uint64_t n, const FastVariant::stream &s) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  FastVariant::stream _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t k = _loop_n - 1;
      const auto &[a0, a1] =
          crane::get<typename FastVariant::stream::Cons>(_loop_s.v());
      auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &crane::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = a1;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_root);
}
