#include "loopify_numeric_misc.h"

uint64_t LoopifyNumericMisc::sum_abs(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_abs: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_sum_abs_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_abs_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_abs_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_abs_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::alternating_ops(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of alternating_ops: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_alternating_ops_in_false {
    uint64_t n_;
  };

  struct _after_alternating_ops_in_true {
    uint64_t n_;
  };

  using _frame = std::variant<_call, _after_alternating_ops_in_false,
                              _after_alternating_ops_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if ((UINT64_C(2) ? ((n_ + 1)) % UINT64_C(2) : (n_ + 1)) ==
            UINT64_C(0)) {
          _stack.emplace_back(_after_alternating_ops_in_true{n_});
        } else {
          _stack.emplace_back(_after_alternating_ops_in_false{n_});
        }
        _stack.emplace_back(_call{n_});
      }
    } else if (std::holds_alternative<_after_alternating_ops_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_alternating_ops_in_false>(_popped));
      _stack.pop_back();
      uint64_t n_ = _f.n_;
      _result = ((n_ + 1)) * UINT64_C(2) + _result;
    } else {
      auto _f = std::move(std::get<_after_alternating_ops_in_true>(_popped));
      _stack.pop_back();
      uint64_t n_ = _f.n_;
      _result = ((n_ + 1)) + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::count_even(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of count_even: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_count_even_in_true {};

  using _frame = std::variant<_call, _after_count_even_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          _stack.emplace_back(_after_count_even_in_true{});
        }
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_count_even_in_true>(_popped));
      _stack.pop_back();
      _result = UINT64_C(1) + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::count_odd(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of count_odd: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_count_odd_in_true {};

  using _frame = std::variant<_call, _after_count_odd_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(1)) {
          _stack.emplace_back(_after_count_odd_in_true{});
        }
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_count_odd_in_true>(_popped));
      _stack.pop_back();
      _result = UINT64_C(1) + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::product(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of product: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_product_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_product_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_product_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_product_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 * _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::sum_of_squares(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_of_squares: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_sum_of_squares_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_of_squares_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_of_squares_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_of_squares_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 * a0 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::max_two(uint64_t a, uint64_t b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}

uint64_t LoopifyNumericMisc::list_max(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of list_max: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_list_max_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_list_max_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_list_max_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_list_max_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = max_two(a0, _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::list_min(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of list_min: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_list_min_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_list_min_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_list_min_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_list_min_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t min_rest = _result;
      if (a0 < min_rest) {
        _result = a0;
      } else {
        _result = min_rest;
      }
    }
  }
  return _result;
}
