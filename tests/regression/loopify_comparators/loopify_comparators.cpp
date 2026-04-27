#include <loopify_comparators.h>

__attribute__((pure)) unsigned int
LoopifyComparators::maximum_by(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int m = _result;
      if (m < d_a0) {
        _result = d_a0;
      } else {
        _result = m;
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyComparators::minimum_by(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int m = _result;
      if (d_a0 < m) {
        _result = d_a0;
      } else {
        _result = m;
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int> LoopifyComparators::merge_by_fuel(
    const unsigned int &fuel, List<unsigned int> l1, List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          if (d_a0 <= d_a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l1 = *(d_a1);
            unsigned int _next_fuel = fuel_;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a00, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l2 = *(d_a10);
            unsigned int _next_fuel = fuel_;
            _loop_l2 = std::move(_next_l2);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyComparators::merge_by(const List<unsigned int> &l1,
                             const List<unsigned int> &l2) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  return merge_by_fuel((len1 + len2), l1, l2);
}

__attribute__((pure)) List<unsigned int>
LoopifyComparators::insert_sorted(unsigned int x, List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (x <= d_a0) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(x, _loop_l));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyComparators::insertion_sort(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = insert_sorted(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyComparators::is_sorted_fuel(const unsigned int &fuel,
                                   const List<unsigned int> &l) {
  bool _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = true;
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = true;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          _result = true;
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (d_a0 <= d_a00) {
            List<unsigned int> _next_l =
                List<unsigned int>::cons(d_a00, *(d_a10));
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          } else {
            _result = false;
            break;
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyComparators::is_sorted(const List<unsigned int> &l) {
  unsigned int len = l.length();
  return is_sorted_fuel(len, l);
}
