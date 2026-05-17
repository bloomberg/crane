#include "loopify_extrema.h"

unsigned int LoopifyExtrema::maximum(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified maximum: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int max_rest = _result;
      if (max_rest < a0) {
        _result = std::move(a0);
      } else {
        _result = std::move(max_rest);
      }
    }
  }
  return _result;
}

unsigned int LoopifyExtrema::minimum(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified minimum: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int min_rest = _result;
      if (a0 < min_rest) {
        _result = std::move(a0);
      } else {
        _result = std::move(min_rest);
      }
    }
  }
  return _result;
}

std::pair<unsigned int, unsigned int> LoopifyExtrema::minmax(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified minmax: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = std::make_pair(a0, a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      const unsigned int &lo = _result.first;
      const unsigned int &hi = _result.second;
      _result = std::make_pair(std::min(a0, lo), std::max(a0, hi));
    }
  }
  return _result;
}

unsigned int LoopifyExtrema::lex_compare(const List<unsigned int> &l1,
                                         const List<unsigned int> &l2) {
  unsigned int _result;
  const List<unsigned int> *_loop_l2 = &l2;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = 0u;
        break;
      } else {
        _result = 1u;
        break;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = 2u;
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        if (a0 < a00) {
          _result = 1u;
          break;
        } else {
          if (a00 < a0) {
            _result = 2u;
            break;
          } else {
            _loop_l2 = a10.get();
            _loop_l1 = a1.get();
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifyExtrema::all_equal(const List<unsigned int> &l) {
  bool _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        _result = true;
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
        } else {
          _result = false;
          break;
        }
      }
    }
  }
  return _result;
}

bool LoopifyExtrema::is_sorted(const List<unsigned int> &l) {
  bool _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        _result = true;
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (a0 <= a00) {
          _loop_l = a1.get();
        } else {
          _result = false;
          break;
        }
      }
    }
  }
  return _result;
}
