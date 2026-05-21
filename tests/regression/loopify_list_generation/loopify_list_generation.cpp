#include "loopify_list_generation.h"

List<uint64_t> LoopifyListGeneration::replicate(uint64_t n, uint64_t x) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListGeneration::stutter(const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      auto _cell1 = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).l =
          std::move(_cell1);
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>(
                    std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                        .l->v_mut())
                    .l;
      _loop_l = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListGeneration::cycle(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [l], resumes after recursive call with _result.
  struct _Resume_n_ {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified cycle: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{l});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = _f.l.app(_result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::iterate(uint64_t n, uint64_t x) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_x = std::move(x);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_x = (_loop_x + UINT64_C(1));
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListGeneration::replicate_list(
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume_n: saves [rep], resumes after recursive call with _result.
  struct _Resume_n {
    List<uint64_t> rep;
  };

  using _Frame = std::variant<_Enter, _Resume_n>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified replicate_list: _Enter -> _Resume_n.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const uint64_t &n = a0.first;
        const uint64_t &x = a0.second;
        List<uint64_t> rep = replicate(n, x);
        _stack.emplace_back(_Resume_n{std::move(rep)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n>(_frame));
      _result = _f.rep.app(_result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::repeat_with_sep(uint64_t sep, uint64_t n,
                                                      uint64_t x) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (n_ <= 0) {
        *_write = std::make_shared<List<uint64_t>>(
            List<uint64_t>::cons(x, List<uint64_t>::nil()));
        break;
      } else {
        uint64_t _x = n_ - 1;
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(x, nullptr));
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).l =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .l->v_mut())
                 .l;
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListGeneration::range(uint64_t start, uint64_t len) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_len = std::move(len);
  uint64_t _loop_start = std::move(start);
  while (true) {
    if (_loop_len <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t len_ = _loop_len - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_len = len_;
      _loop_start = (_loop_start + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_head);
}
