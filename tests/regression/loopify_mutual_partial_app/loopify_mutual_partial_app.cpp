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

  /// _After_Add: saves [a0], dispatches next recursive call.
  struct _After_Add {
    const LoopifyMutualPartialApp::e<uint64_t> *a0;
  };

  /// _Combine_Add: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Add {
    uint64_t _result;
  };

  /// _Resume_MConst: saves [_inl_u0], resumes after recursive call with
  /// _result.
  struct _Resume_MConst {
    uint64_t _inl_u0;
  };

  using _Frame = std::variant<_Enter, _After_Add, _Combine_Add, _Resume_MConst>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&x});
  /// Loopified sum_e: _Enter -> _After_Add -> _Combine_Add -> _Resume_MConst.
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
        _stack.emplace_back(_After_Add{crane_raw(a0)});
        _stack.emplace_back(_Enter{crane_raw(b0)});
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
          _stack.emplace_back(_Resume_MConst{_inl_u0});
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
          _result = (sum_md(*_inl_a0) + sum_md(*_inl_b0));
        }
      }
    } else if (std::holds_alternative<_After_Add>(_frame)) {
      auto _f = std::move(std::get<_After_Add>(_frame));
      _stack.emplace_back(_Combine_Add{std::move(_result)});
      _stack.emplace_back(_Enter{_f.a0});
    } else if (std::holds_alternative<_Combine_Add>(_frame)) {
      auto _f = std::move(std::get<_Combine_Add>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Resume_MConst>(_frame));
      _result = (_f._inl_u0 + std::move(_result));
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

  /// _After_MPair: saves [a0], dispatches next recursive call.
  struct _After_MPair {
    LoopifyMutualPartialApp::md<uint64_t> a0;
  };

  /// _Combine_MPair: receives partial results, combines with _result from final
  /// call.
  struct _Combine_MPair {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_MPair, _Combine_MPair>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{m});
  /// Loopified sum_md: _Enter -> _After_MPair -> _Combine_MPair.
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
        _result = (u0 + sum_e(*x0));
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
        _stack.emplace_back(_After_MPair{*a0});
        _stack.emplace_back(_Enter{*b0});
      }
    } else if (std::holds_alternative<_After_MPair>(_frame)) {
      auto _f = std::move(std::get<_After_MPair>(_frame));
      _stack.emplace_back(_Combine_MPair{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f.a0)});
    } else {
      auto _f = std::move(std::get<_Combine_MPair>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
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
