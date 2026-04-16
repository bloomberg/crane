#include <loopify_comparators.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int
LoopifyComparators::maximum_by(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a1->v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
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
LoopifyComparators::minimum_by(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a1->v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
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

std::shared_ptr<List<unsigned int>>
LoopifyComparators::merge_by_fuel(const unsigned int fuel,
                                  std::shared_ptr<List<unsigned int>> l1,
                                  std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              std::move(_loop_l2);
        } else {
          _head = std::move(_loop_l2);
        }
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                std::move(_loop_l1);
          } else {
            _head = std::move(_loop_l1);
          }
          _continue = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
          if (d_a0 <= d_a00) {
            auto _cell = List<unsigned int>::cons(d_a0, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
            unsigned int _next_fuel = fuel_;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = List<unsigned int>::cons(d_a00, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
            unsigned int _next_fuel = fuel_;
            _loop_l2 = std::move(_next_l2);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyComparators::merge_by(const std::shared_ptr<List<unsigned int>> &l1,
                             const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  return merge_by_fuel((len1 + len2), l1, l2);
}

std::shared_ptr<List<unsigned int>>
LoopifyComparators::insert_sorted(const unsigned int x,
                                  std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(x, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(x, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x <= d_a0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(x, _loop_l);
        } else {
          _head = List<unsigned int>::cons(x, _loop_l);
        }
        _continue = false;
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyComparators::insertion_sort(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = insert_sorted(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) bool LoopifyComparators::is_sorted_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      _result = true;
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = true;
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a1->v())) {
          _result = true;
          _continue = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(d_a1->v());
          if (d_a0 <= d_a00) {
            std::shared_ptr<List<unsigned int>> _next_l =
                List<unsigned int>::cons(d_a00, d_a10);
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          } else {
            _result = false;
            _continue = false;
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyComparators::is_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return is_sorted_fuel(len, l);
}
