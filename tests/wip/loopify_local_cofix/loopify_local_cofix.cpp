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
  {
    uint64_t _lc1_n = UINT64_C(0);

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      uint64_t n;
    };

    using CraneFrame = std::variant<CraneEnter>;
    LoopifyLocalCofix::stream _lc1_result{};
    crane::small_vector<CraneFrame> _lc1_stack;
    _lc1_stack.emplace_back(CraneEnter{_lc1_n});
    /// Loopified go: CraneEnter.
    while (!_lc1_stack.empty()) {
      CraneFrame _frame = std::move(_lc1_stack.back());
      _lc1_stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t _lc1_n = _f.n;
      _lc1_result =
          stream::lazy_([=]() -> typename LoopifyLocalCofix::stream::Cons {
            return {(l.length() + _lc1_n), _self_go(_self_go, (_lc1_n + 1))};
          });
    }
    return _lc1_result;
  }
}
