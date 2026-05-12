#include "loopify_list_generation.h"

List<unsigned int> LoopifyListGeneration::replicate(const unsigned int n,
                                                    const unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(x, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListGeneration::stutter(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      auto _cell1 = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
          std::move(_cell1);
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>(
               std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1->v_mut())
               .d_a1;
      _loop_l = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListGeneration::cycle(
    const unsigned int n,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_n_: saves [l], resumes after recursive call with _result.
  struct _Resume_n_ {
    List<unsigned int> l;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(n));
  /// Loopified cycle: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Resume_n_(l));
        _stack.emplace_back(_Enter(n_));
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = _f.l.app(_result);
    }
  }
  return _result;
}

List<unsigned int> LoopifyListGeneration::iterate(const unsigned int n,
                                                  const unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_x = x;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_x, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_x = (_loop_x + 1u);
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListGeneration::replicate_list(
    const List<std::pair<unsigned int, unsigned int>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<unsigned int, unsigned int>> *l;
  };

  /// _Resume_n: saves [rep], resumes after recursive call with _result.
  struct _Resume_n {
    List<unsigned int> rep;
  };

  using _Frame = std::variant<_Enter, _Resume_n>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(&l));
  /// Loopified replicate_list: _Enter -> _Resume_n.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<unsigned int, unsigned int>> &l = *(_f.l);
      if (std::holds_alternative<
              typename List<std::pair<unsigned int, unsigned int>>::Nil>(
              l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<
            typename List<std::pair<unsigned int, unsigned int>>::Cons>(l.v());
        const unsigned int &n = d_a0.first;
        const unsigned int &x = d_a0.second;
        List<unsigned int> rep = replicate(n, x);
        _stack.emplace_back(_Resume_n(std::move(rep)));
        _stack.emplace_back(_Enter(d_a1.get()));
      }
    } else {
      auto _f = std::move(std::get<_Resume_n>(_frame));
      _result = _f.rep.app(_result);
    }
  }
  return _result;
}

List<unsigned int> LoopifyListGeneration::repeat_with_sep(
    const unsigned int sep, const unsigned int n, const unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (n_ <= 0) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(x, List<unsigned int>::nil()));
        break;
      } else {
        unsigned int _x = n_ - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(x, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(sep, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListGeneration::range(const unsigned int start,
                                                const unsigned int len) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_len = len;
  unsigned int _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int len_ = _loop_len - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_start, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_len = len_;
      _loop_start = (_loop_start + 1u);
      continue;
    }
  }
  return std::move(*(_head));
}
