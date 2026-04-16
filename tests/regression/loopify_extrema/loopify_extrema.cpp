#include <loopify_extrema.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int
LoopifyExtrema::maximum(const std::shared_ptr<List<unsigned int>> &l) {
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
      unsigned int max_rest = _result;
      if (max_rest < d_a0) {
        _result = d_a0;
      } else {
        _result = max_rest;
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyExtrema::minimum(const std::shared_ptr<List<unsigned int>> &l) {
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
      unsigned int min_rest = _result;
      if (d_a0 < min_rest) {
        _result = d_a0;
      } else {
        _result = min_rest;
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyExtrema::minmax(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a1->v())) {
          _result = std::make_pair(d_a0, d_a0);
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
      const unsigned int &lo = _result.first;
      const unsigned int &hi = _result.second;
      _result = std::make_pair(std::min(d_a0, lo), std::max(d_a0, hi));
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyExtrema::lex_compare(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = 0u;
        _continue = false;
      } else {
        _result = 1u;
        _continue = false;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = 2u;
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        if (d_a0 < d_a00) {
          _result = 1u;
          _continue = false;
        } else {
          if (d_a00 < d_a0) {
            _result = 2u;
            _continue = false;
          } else {
            std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
            std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyExtrema::all_equal(const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        _result = true;
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(d_a1->v());
        if (d_a0 == d_a00) {
          _loop_l = d_a1;
        } else {
          _result = false;
          _continue = false;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyExtrema::is_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        _result = true;
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(d_a1->v());
        if (d_a0 <= d_a00) {
          _loop_l = d_a1;
        } else {
          _result = false;
          _continue = false;
        }
      }
    }
  }
  return _result;
}
