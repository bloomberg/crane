#include <loopify_list_access.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int
LoopifyListAccess::nth(const unsigned int n,
                       const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_n == 0u) {
        _result = d_a0;
        _continue = false;
      } else {
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::last(const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        _result = d_a0;
        _continue = false;
      } else {
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::index_of_aux(const unsigned int x,
                                const std::shared_ptr<List<unsigned int>> &l,
                                const unsigned int idx) {
  unsigned int _result;
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x == d_a0) {
        _result = _loop_idx;
        _continue = false;
      } else {
        unsigned int _next_idx = (_loop_idx + 1u);
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::index_of(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  return index_of_aux(x, l, 0u);
}

__attribute__((pure)) bool
LoopifyListAccess::member(const unsigned int x,
                          const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x == d_a0) {
        _result = true;
        _continue = false;
      } else {
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListAccess::lookup(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  unsigned int _result;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        _result = v;
        _continue = false;
      } else {
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListAccess::lookup_all(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        auto _cell = List<unsigned int>::cons(v, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = d_a1;
        continue;
      } else {
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::count(const unsigned int x,
                         const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
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
        if (x == d_a0) {
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{d_a1});
        } else {
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyListAccess::elem_at_eq(const unsigned int idx, const unsigned int val,
                              const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_idx == 0u) {
        _result = d_a0 == val;
        _continue = false;
      } else {
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_idx =
            (((_loop_idx - 1u) > _loop_idx ? 0 : (_loop_idx - 1u)));
        _loop_l = std::move(_next_l);
        _loop_idx = std::move(_next_idx);
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::nth_default(const unsigned int n,
                               const unsigned int default0,
                               const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = default0;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_n == 0u) {
        _result = d_a0;
        _continue = false;
      } else {
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}
