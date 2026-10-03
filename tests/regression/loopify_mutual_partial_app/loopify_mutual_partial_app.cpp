#include "loopify_mutual_partial_app.h"

/// A polymorphic mutual traversal in the shape of Vellvm's
/// Traversal.ft_exp / ft_metadata: a class parameter (Endo), a function
/// parameter f, a local closure over the recursion (ftpair), and the
/// mutual partner partially applied under map (map (ft_md U V f) l).
/// With Set Crane Loopify the generated loop binds a non-const lvalue
/// reference to a moved temporary ("non-const lvalue reference to type
/// '(lambda ...)' cannot bind to a temporary") and calls ft_e with
/// arguments it has no overload for.
///
/// loopify_mutual_result_types (fixed in a9df8ed7e) is the same pair
/// without the parameters; this is what is left of Vellvm's global
/// Set Crane Loopify on 19ffa36ec: all 4 of its remaining errors.
uint64_t LoopifyMutualPartialApp::sum_e(
    const LoopifyMutualPartialApp::e<uint64_t>
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMutualPartialApp::e<uint64_t> *x;
  };

  /// _Enter_inl: captures varying parameters for each recursive call.
  struct _Enter_inl {
    LoopifyMutualPartialApp::md<uint64_t> _inl_m;
  };

  /// _Cont_Add: saves [b0], resumes after recursive call, then processes rest.
  struct _Cont_Add {
    const LoopifyMutualPartialApp::e<uint64_t> *b0;
  };

  /// _Cont_Add_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Add_1 {
    uint64_t _tmp2;
  };

  /// _Cont_MConst: saves [_inl_u0], resumes after recursive call, then
  /// processes rest.
  struct _Cont_MConst {
    uint64_t _inl_u0;
  };

  /// _Cont_MConst_1: saves [_inl_u0], resumes after recursive call, then
  /// processes rest.
  struct _Cont_MConst_1 {
    uint64_t _inl_u0;
  };

  /// _Cont_MPair: saves [_inl_b0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MPair {
    std::shared_ptr<LoopifyMutualPartialApp::md<uint64_t>> _inl_b0;
  };

  /// _Cont_MPair_1: saves [_inl__tmp4], resumes after recursive call, then
  /// processes rest.
  struct _Cont_MPair_1 {
    uint64_t _inl__tmp4;
  };

  using _Frame =
      std::variant<_Enter, _Enter_inl, _Cont_Add, _Cont_Add_1, _Cont_MConst,
                   _Cont_MConst_1, _Cont_MPair, _Cont_MPair_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&x});
  /// Loopified sum_e: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_MConst ->
  /// _Cont_MConst_1 -> _Cont_MPair -> _Cont_MPair_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMutualPartialApp::e<uint64_t> &x = *_f.x;
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(
                x.v());
        _result = std::move(n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(
                     x.v())) {
        const auto &[u0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(x.v());
        _result = std::move(u0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Add>(
                     x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Add>(x.v());
        _stack.emplace_back(_Cont_Add{crane_raw(b0)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Meta>(
                x.v());
        const LoopifyMutualPartialApp::md<uint64_t> &_inl_m = *m0;
        if (std::holds_alternative<
                typename LoopifyMutualPartialApp::md<uint64_t>::MNull>(
                _inl_m.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                       _inl_m.v())) {
          const auto &[_inl_u0, _inl_x0] =
              std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                  _inl_m.v());
          _stack.emplace_back(_Cont_MConst{_inl_u0});
          _stack.emplace_back(_Enter{crane_raw(_inl_x0)});
        } else if (std::holds_alternative<
                       typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                       _inl_m.v())) {
          const auto &[_inl_l0] =
              std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                  _inl_m.v());
          const List<LoopifyMutualPartialApp::md<uint64_t>> &_inl_l0_value =
              *_inl_l0;
          _result = _inl_l0_value.template fold_left<uint64_t>(
              [](uint64_t acc,
                 const LoopifyMutualPartialApp::md<uint64_t> &m0) {
                return (acc + sum_md(m0));
              },
              UINT64_C(0));
        } else {
          const auto &[_inl_a0, _inl_b0] =
              std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MPair>(
                  _inl_m.v());
          _stack.emplace_back(_Cont_MPair{_inl_b0});
          _stack.emplace_back(_Enter_inl{*_inl_a0});
        }
      }
    } else if (std::holds_alternative<_Enter_inl>(_frame)) {
      auto _f = std::move(std::get<_Enter_inl>(_frame));
      const LoopifyMutualPartialApp::md<uint64_t> &_inl_m =
          std::move(_f._inl_m);
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::md<uint64_t>::MNull>(
              _inl_m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                     _inl_m.v())) {
        const auto &[_inl_u0, _inl_x0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                _inl_m.v());
        _stack.emplace_back(_Cont_MConst_1{_inl_u0});
        _stack.emplace_back(_Enter{crane_raw(_inl_x0)});
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                     _inl_m.v())) {
        const auto &[_inl_l0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                _inl_m.v());
        const List<LoopifyMutualPartialApp::md<uint64_t>> &_inl_l0_value =
            *_inl_l0;
        _result = _inl_l0_value.template fold_left<uint64_t>(
            [](uint64_t acc, const LoopifyMutualPartialApp::md<uint64_t> &m0) {
              return (acc + sum_md(m0));
            },
            UINT64_C(0));
      } else {
        const auto &[_inl_a0, _inl_b0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MPair>(
                _inl_m.v());
        uint64_t _inl__tmp4 = sum_md(*_inl_a0);
        uint64_t _inl__tmp3 = sum_md(*_inl_b0);
        _result = (_inl__tmp4 + _inl__tmp3);
      }
    } else if (std::holds_alternative<_Cont_Add>(_frame)) {
      auto _f = std::move(std::get<_Cont_Add>(_frame));
      const LoopifyMutualPartialApp::e<uint64_t> &b0 = *_f.b0;
      _stack.emplace_back(_Cont_Add_1{std::move(_result)});
      _stack.emplace_back(_Enter{&b0});
    } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Add_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    } else if (std::holds_alternative<_Cont_MConst>(_frame)) {
      auto _f = std::move(std::get<_Cont_MConst>(_frame));
      uint64_t _inl_u0 = _f._inl_u0;
      uint64_t _inl__tmp1 = std::move(_result);
      _result = (_inl_u0 + _inl__tmp1);
    } else if (std::holds_alternative<_Cont_MConst_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_MConst_1>(_frame));
      uint64_t _inl_u0 = _f._inl_u0;
      uint64_t _inl__tmp1 = std::move(_result);
      _result = (_inl_u0 + _inl__tmp1);
    } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
      auto _f = std::move(std::get<_Cont_MPair>(_frame));
      std::shared_ptr<LoopifyMutualPartialApp::md<uint64_t>> _inl_b0 =
          std::move(_f._inl_b0);
      uint64_t _inl__tmp4 = std::move(_result);
      _stack.emplace_back(_Cont_MPair_1{_inl__tmp4});
      _stack.emplace_back(_Enter_inl{*_inl_b0});
    } else {
      auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
      uint64_t _inl__tmp4 = _f._inl__tmp4;
      uint64_t _inl__tmp3 = std::move(_result);
      _result = (_inl__tmp4 + _inl__tmp3);
    }
  }
  return _result;
}

uint64_t LoopifyMutualPartialApp::sum_md(
    const LoopifyMutualPartialApp::md<uint64_t>
        &m) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyMutualPartialApp::md<uint64_t> m;
  };

  /// _Enter_inl: captures varying parameters for each recursive call.
  struct _Enter_inl {
    LoopifyMutualPartialApp::e<uint64_t> _inl_x;
  };

  /// _Cont_MConst: saves [u0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MConst {
    uint64_t u0;
  };

  /// _Cont_MPair: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MPair {
    std::shared_ptr<LoopifyMutualPartialApp::md<uint64_t>> b0;
  };

  /// _Cont_MPair_1: saves [_tmp4], resumes after recursive call, then processes
  /// rest.
  struct _Cont_MPair_1 {
    uint64_t _tmp4;
  };

  using _Frame = std::variant<_Enter, _Enter_inl, _Cont_MConst, _Cont_MPair,
                              _Cont_MPair_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{m});
  /// Loopified sum_md: _Enter -> _Cont_MConst -> _Cont_MPair -> _Cont_MPair_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMutualPartialApp::md<uint64_t> &m = std::move(_f.m);
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::md<uint64_t>::MNull>(m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                     m.v())) {
        const auto &[u0, x0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                m.v());
        _stack.emplace_back(_Cont_MConst{u0});
        _stack.emplace_back(_Enter_inl{*x0});
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                     m.v())) {
        const auto &[l0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                m.v());
        const List<LoopifyMutualPartialApp::md<uint64_t>> &l0_value = *l0;
        _result = l0_value.template fold_left<uint64_t>(
            [](uint64_t acc, const LoopifyMutualPartialApp::md<uint64_t> &m0) {
              return (acc + sum_md(m0));
            },
            UINT64_C(0));
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MPair>(
                m.v());
        _stack.emplace_back(_Cont_MPair{b0});
        _stack.emplace_back(_Enter{*a0});
      }
    } else if (std::holds_alternative<_Enter_inl>(_frame)) {
      auto _f = std::move(std::get<_Enter_inl>(_frame));
      const LoopifyMutualPartialApp::e<uint64_t> &_inl_x = std::move(_f._inl_x);
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(
              _inl_x.v())) {
        const auto &[_inl_n0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(
                _inl_x.v());
        _result = std::move(_inl_n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(
                     _inl_x.v())) {
        const auto &[_inl_u0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(
                _inl_x.v());
        _result = std::move(_inl_u0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Add>(
                     _inl_x.v())) {
        const auto &[_inl_a0, _inl_b0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Add>(
                _inl_x.v());
        uint64_t _inl__tmp2 = sum_e(*_inl_a0);
        uint64_t _inl__tmp1 = sum_e(*_inl_b0);
        _result = (_inl__tmp2 + _inl__tmp1);
      } else {
        const auto &[_inl_m0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Meta>(
                _inl_x.v());
        _stack.emplace_back(_Enter{*_inl_m0});
      }
    } else if (std::holds_alternative<_Cont_MConst>(_frame)) {
      auto _f = std::move(std::get<_Cont_MConst>(_frame));
      uint64_t u0 = _f.u0;
      _result = (u0 + std::move(_result));
    } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
      auto _f = std::move(std::get<_Cont_MPair>(_frame));
      std::shared_ptr<LoopifyMutualPartialApp::md<uint64_t>> b0 =
          std::move(_f.b0);
      _stack.emplace_back(_Cont_MPair_1{std::move(_result)});
      _stack.emplace_back(_Enter{*b0});
    } else {
      auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
      _result = (_f._tmp4 + std::move(_result));
    }
  }
  return _result;
}

/// leaves doubled: 2*(1+2+4) = 14; tags and consts +100 each: 107 + 105 + 101 =
/// 313
bool LoopifyMutualPartialApp::check(std::monostate) {
  return sum_e(ft_e<uint64_t, uint64_t>(
             endo_double, [](uint64_t u) { return (u + UINT64_C(100)); },
             sample)) == (UINT64_C(14) + UINT64_C(313));
}
