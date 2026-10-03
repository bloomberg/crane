#include "fast_variant.h"

FastVariant::tree FastVariant::build(const List<uint64_t> &l) {
  return l.template fold_right<FastVariant::tree>(
      [](const uint64_t &_x0, const FastVariant::tree &_x1) {
        return _x1.insert(_x0);
      },
      tree::leaf());
}

FastVariant::stream
FastVariant::from(uint64_t n) { /// _Enter: captures varying parameters for each
                                /// recursive call.

  struct _Enter {
    uint64_t n;
  };

  using _Frame = crane::variant<_Enter>;
  FastVariant::stream _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified from: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(crane::get<_Enter>(_frame));
    uint64_t n = _f.n;
    _result = stream::lazy_([=]() -> FastVariant::stream {
      return stream::cons(n, from((n + 1)));
    });
  }
  return _result;
}

List<uint64_t> FastVariant::take(uint64_t n, FastVariant::stream s) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  FastVariant::stream _loop_s = std::move(s);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t k = _loop_n - 1;
      const auto &[a0, a1] =
          crane::get<typename FastVariant::stream::Cons>(_loop_s.v());
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &crane::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_s = a1;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_head);
}
