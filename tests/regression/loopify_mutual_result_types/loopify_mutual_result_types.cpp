#include "loopify_mutual_result_types.h"

/// dbl_e and dbl_md are mutually recursive and return different types
/// (e and md).  With Set Crane Loopify, dbl_e becomes a frame-stack
/// loop that inlines dbl_md as extra frames (_Enter_inl), but both halves
/// store into the one _result variable, declared at dbl_e's result type:
/// _result = Md::mnull(); assigns an md to an e -- "no viable
/// overloaded '='" -- and the resume frame then hands that _result to a
/// constructor expecting the other type.
///
/// Found in Vellvm with the global Set Crane Loopify:
/// Traversal.ft_exp / ft_metadata, 4 of its 59 errors.
LoopifyMutualResultTypes::e LoopifyMutualResultTypes::dbl_e(
    const LoopifyMutualResultTypes::e
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyMutualResultTypes::e x;
  };

  /// _After_Add: saves [a0], dispatches next recursive call.
  struct _After_Add {
    LoopifyMutualResultTypes::e a0;
  };

  /// _Combine_Add: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Add {
    LoopifyMutualResultTypes::e _result;
  };

  using _Frame = std::variant<_Enter, _After_Add, _Combine_Add>;
  LoopifyMutualResultTypes::e _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{x});
  /// Loopified dbl_e: _Enter -> _After_Add -> _Combine_Add.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMutualResultTypes::e &x = std::move(_f.x);
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = e::leaf((UINT64_C(2) * n0));
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::e::Add>(x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(_After_Add{*a0});
        _stack.emplace_back(_Enter{*b0});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        _result = e::meta([](const LoopifyMutualResultTypes::md &_inl_m)
                              -> LoopifyMutualResultTypes::md {
          if (std::holds_alternative<
                  typename LoopifyMutualResultTypes::md::MNull>(_inl_m.v())) {
            return md::mnull();
          } else if (std::holds_alternative<
                         typename LoopifyMutualResultTypes::md::MConst>(
                         _inl_m.v())) {
            const auto &[_inl_x0] =
                std::get<typename LoopifyMutualResultTypes::md::MConst>(
                    _inl_m.v());
            return md::mconst(dbl_e(*_inl_x0));
          } else {
            const auto &[_inl_a0, _inl_b0] =
                std::get<typename LoopifyMutualResultTypes::md::MPair>(
                    _inl_m.v());
            return md::mpair(dbl_md(*_inl_a0), dbl_md(*_inl_b0));
          }
        }(*m0));
      }
    } else if (std::holds_alternative<_After_Add>(_frame)) {
      auto _f = std::move(std::get<_After_Add>(_frame));
      _stack.emplace_back(_Combine_Add{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f.a0)});
    } else {
      auto _f = std::move(std::get<_Combine_Add>(_frame));
      _result = e::add(std::move(_result), std::move(_f._result));
    }
  }
  return _result;
}

LoopifyMutualResultTypes::md LoopifyMutualResultTypes::dbl_md(
    const LoopifyMutualResultTypes::md
        &m) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyMutualResultTypes::md m;
  };

  /// _After_MPair: saves [a0], dispatches next recursive call.
  struct _After_MPair {
    LoopifyMutualResultTypes::md a0;
  };

  /// _Combine_MPair: receives partial results, combines with _result from final
  /// call.
  struct _Combine_MPair {
    LoopifyMutualResultTypes::md _result;
  };

  using _Frame = std::variant<_Enter, _After_MPair, _Combine_MPair>;
  LoopifyMutualResultTypes::md _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{m});
  /// Loopified dbl_md: _Enter -> _After_MPair -> _Combine_MPair.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMutualResultTypes::md &m = std::move(_f.m);
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = md::mnull();
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::md::MConst>(m.v())) {
        const auto &[x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        _result = md::mconst([](const LoopifyMutualResultTypes::e &_inl_x)
                                 -> LoopifyMutualResultTypes::e {
          if (std::holds_alternative<
                  typename LoopifyMutualResultTypes::e::Leaf>(_inl_x.v())) {
            const auto &[_inl_n0] =
                std::get<typename LoopifyMutualResultTypes::e::Leaf>(
                    _inl_x.v());
            return e::leaf((UINT64_C(2) * _inl_n0));
          } else if (std::holds_alternative<
                         typename LoopifyMutualResultTypes::e::Add>(
                         _inl_x.v())) {
            const auto &[_inl_a0, _inl_b0] =
                std::get<typename LoopifyMutualResultTypes::e::Add>(_inl_x.v());
            return e::add(dbl_e(*_inl_a0), dbl_e(*_inl_b0));
          } else {
            const auto &[_inl_m0] =
                std::get<typename LoopifyMutualResultTypes::e::Meta>(
                    _inl_x.v());
            return e::meta(dbl_md(*_inl_m0));
          }
        }(*x0));
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(_After_MPair{*a0});
        _stack.emplace_back(_Enter{*b0});
      }
    } else if (std::holds_alternative<_After_MPair>(_frame)) {
      auto _f = std::move(std::get<_After_MPair>(_frame));
      _stack.emplace_back(_Combine_MPair{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f.a0)});
    } else {
      auto _f = std::move(std::get<_Combine_MPair>(_frame));
      _result = md::mpair(std::move(_result), std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyMutualResultTypes::sum_e(
    const LoopifyMutualResultTypes::e
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMutualResultTypes::e *x;
  };

  /// _Enter_inl: captures varying parameters for each recursive call.
  struct _Enter_inl {
    LoopifyMutualResultTypes::md _inl_m;
  };

  /// _Cont_Add: saves [b0], resumes after recursive call, then processes rest.
  struct _Cont_Add {
    const LoopifyMutualResultTypes::e *b0;
  };

  /// _Cont_Add_1: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Add_1 {
    uint64_t r_;
  };

  /// _Cont_MPair: saves [_inl_b0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MPair {
    std::shared_ptr<LoopifyMutualResultTypes::md> _inl_b0;
  };

  /// _Cont_MPair_1: saves [_inl_r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_MPair_1 {
    uint64_t _inl_r_;
  };

  using _Frame = std::variant<_Enter, _Enter_inl, _Cont_Add, _Cont_Add_1,
                              _Cont_MPair, _Cont_MPair_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&x});
  /// Loopified sum_e: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_MPair ->
  /// _Cont_MPair_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMutualResultTypes::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = std::move(n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::e::Add>(x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(_Cont_Add{crane_raw(b0)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        const LoopifyMutualResultTypes::md &_inl_m = *m0;
        if (std::holds_alternative<
                typename LoopifyMutualResultTypes::md::MNull>(_inl_m.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::md::MConst>(
                       _inl_m.v())) {
          const auto &[_inl_x0] =
              std::get<typename LoopifyMutualResultTypes::md::MConst>(
                  _inl_m.v());
          _stack.emplace_back(_Enter{crane_raw(_inl_x0)});
        } else {
          const auto &[_inl_a0, _inl_b0] =
              std::get<typename LoopifyMutualResultTypes::md::MPair>(
                  _inl_m.v());
          _stack.emplace_back(_Cont_MPair{_inl_b0});
          _stack.emplace_back(_Enter_inl{*_inl_a0});
        }
      }
    } else if (std::holds_alternative<_Enter_inl>(_frame)) {
      auto _f = std::move(std::get<_Enter_inl>(_frame));
      const LoopifyMutualResultTypes::md &_inl_m = std::move(_f._inl_m);
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              _inl_m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::md::MConst>(
                     _inl_m.v())) {
        const auto &[_inl_x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(_inl_m.v());
        _stack.emplace_back(_Enter{crane_raw(_inl_x0)});
      } else {
        const auto &[_inl_a0, _inl_b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(_inl_m.v());
        uint64_t _inl_r_ = sum_md(*_inl_a0);
        uint64_t _inl_r_0 = sum_md(*_inl_b0);
        _result = (_inl_r_ + _inl_r_0);
      }
    } else if (std::holds_alternative<_Cont_Add>(_frame)) {
      auto _f = std::move(std::get<_Cont_Add>(_frame));
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Add_1{r_});
      _stack.emplace_back(_Enter{&b0});
    } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Add_1>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
      auto _f = std::move(std::get<_Cont_MPair>(_frame));
      std::shared_ptr<LoopifyMutualResultTypes::md> _inl_b0 =
          std::move(_f._inl_b0);
      uint64_t _inl_r_ = std::move(_result);
      _stack.emplace_back(_Cont_MPair_1{_inl_r_});
      _stack.emplace_back(_Enter_inl{*_inl_b0});
    } else {
      auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
      uint64_t _inl_r_ = _f._inl_r_;
      uint64_t _inl_r_0 = std::move(_result);
      _result = (_inl_r_ + _inl_r_0);
    }
  }
  return _result;
}

uint64_t LoopifyMutualResultTypes::sum_md(
    const LoopifyMutualResultTypes::md
        &m) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMutualResultTypes::md *m;
  };

  /// _Enter_inl: captures varying parameters for each recursive call.
  struct _Enter_inl {
    LoopifyMutualResultTypes::e _inl_x;
  };

  /// _Cont_Add: saves [_inl_b0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Add {
    std::shared_ptr<LoopifyMutualResultTypes::e> _inl_b0;
  };

  /// _Cont_Add_1: saves [_inl_r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Add_1 {
    uint64_t _inl_r_;
  };

  /// _Cont_MPair: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MPair {
    const LoopifyMutualResultTypes::md *b0;
  };

  /// _Cont_MPair_1: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MPair_1 {
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Enter_inl, _Cont_Add, _Cont_Add_1,
                              _Cont_MPair, _Cont_MPair_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&m});
  /// Loopified sum_md: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_MPair ->
  /// _Cont_MPair_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::md::MConst>(m.v())) {
        const auto &[x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        const LoopifyMutualResultTypes::e &_inl_x = *x0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
                _inl_x.v())) {
          const auto &[_inl_n0] =
              std::get<typename LoopifyMutualResultTypes::e::Leaf>(_inl_x.v());
          _result = std::move(_inl_n0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::e::Add>(_inl_x.v())) {
          const auto &[_inl_a0, _inl_b0] =
              std::get<typename LoopifyMutualResultTypes::e::Add>(_inl_x.v());
          _stack.emplace_back(_Cont_Add{_inl_b0});
          _stack.emplace_back(_Enter_inl{*_inl_a0});
        } else {
          const auto &[_inl_m0] =
              std::get<typename LoopifyMutualResultTypes::e::Meta>(_inl_x.v());
          _stack.emplace_back(_Enter{crane_raw(_inl_m0)});
        }
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(_Cont_MPair{crane_raw(b0)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Enter_inl>(_frame)) {
      auto _f = std::move(std::get<_Enter_inl>(_frame));
      const LoopifyMutualResultTypes::e &_inl_x = std::move(_f._inl_x);
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              _inl_x.v())) {
        const auto &[_inl_n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(_inl_x.v());
        _result = std::move(_inl_n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::e::Add>(_inl_x.v())) {
        const auto &[_inl_a0, _inl_b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(_inl_x.v());
        uint64_t _inl_r_ = sum_e(*_inl_a0);
        uint64_t _inl_r_0 = sum_e(*_inl_b0);
        _result = (_inl_r_ + _inl_r_0);
      } else {
        const auto &[_inl_m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(_inl_x.v());
        _stack.emplace_back(_Enter{crane_raw(_inl_m0)});
      }
    } else if (std::holds_alternative<_Cont_Add>(_frame)) {
      auto _f = std::move(std::get<_Cont_Add>(_frame));
      std::shared_ptr<LoopifyMutualResultTypes::e> _inl_b0 =
          std::move(_f._inl_b0);
      uint64_t _inl_r_ = std::move(_result);
      _stack.emplace_back(_Cont_Add_1{_inl_r_});
      _stack.emplace_back(_Enter_inl{*_inl_b0});
    } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Add_1>(_frame));
      uint64_t _inl_r_ = _f._inl_r_;
      uint64_t _inl_r_0 = std::move(_result);
      _result = (_inl_r_ + _inl_r_0);
    } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
      auto _f = std::move(std::get<_Cont_MPair>(_frame));
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_MPair_1{r_});
      _stack.emplace_back(_Enter{&b0});
    } else {
      auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    }
  }
  return _result;
}

/// 2 * (1 + 2 + 3 + 4)
bool LoopifyMutualResultTypes::check(std::monostate) {
  return sum_e(dbl_e(sample)) == UINT64_C(20);
}
