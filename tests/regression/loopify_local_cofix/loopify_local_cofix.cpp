#include "loopify_local_cofix.h"

List<uint64_t> LoopifyLocalCofix::take(uint64_t n,
                                       const LoopifyLocalCofix::stream &s) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  LoopifyLocalCofix::stream _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      const auto &[a0, a1] =
          std::get<typename LoopifyLocalCofix::stream::Cons>(_loop_s.v());
      auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

LoopifyLocalCofix::stream LoopifyLocalCofix::from_list(List<uint64_t> l) {
  auto go_impl = [=, l = std::move(l)](
                     auto &_self_go, uint64_t n) -> LoopifyLocalCofix::stream {
    return stream::lazy_([=]() -> typename LoopifyLocalCofix::stream::Cons {
      return {(l.length() + n), _self_go(_self_go, (n + 1))};
    });
  };
  {
    uint64_t _lc1_n = UINT64_C(0);
    return go_impl(go_impl, _lc1_n);
  }
}
