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
uint64_t
LoopifyMutualPartialApp::sum_e(const LoopifyMutualPartialApp::e<uint64_t> &x) {
  // Explicit stack replaces the non-tail recursion of sum_e: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualPartialApp::e<uint64_t> *x;
  };

  struct _after_sum_e_in_Add {
    const LoopifyMutualPartialApp::e<uint64_t> *b0;
  };

  struct _after_sum_e_in_Add_2 {
    uint64_t _tmp2;
  };

  struct _after_sum_e_in_MConst {
    uint64_t u0;
  };

  using _frame = std::variant<_call, _after_sum_e_in_Add, _after_sum_e_in_Add_2,
                              _after_sum_e_in_MConst>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualPartialApp::e<uint64_t> &x = *_f.x;
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(x.v())) {
        const auto &[n0] = std::get<
            typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(x.v());
        _result = std::move(n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(x.v())) {
        const auto &[u0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(x.v());
        _result = std::move(u0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Add>(x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Add>(x.v());
        _stack.emplace_back(_after_sum_e_in_Add{crane_raw(b0)});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else {
        const auto &[m0] = std::get<
            typename LoopifyMutualPartialApp::e<uint64_t>::Meta>(x.v());
        const LoopifyMutualPartialApp::md<uint64_t> &m0_value = *m0;
        if (std::holds_alternative<
                typename LoopifyMutualPartialApp::md<uint64_t>::MNull>(
                m0_value.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                       m0_value.v())) {
          const auto &[u0, x1] =
              std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                  m0_value.v());
          _stack.emplace_back(_after_sum_e_in_MConst{u0});
          _stack.emplace_back(_call{crane_raw(x1)});
        } else if (std::holds_alternative<
                       typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                       m0_value.v())) {
          const auto &[l0] =
              std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                  m0_value.v());
          const List<LoopifyMutualPartialApp::md<uint64_t>> &l0_value = *l0;
          _result = l0_value.template fold_left<uint64_t>(
              [](uint64_t acc,
                 const LoopifyMutualPartialApp::md<uint64_t> &m1) {
                return (acc + sum_md(m1));
              },
              UINT64_C(0));
        } else {
          const auto &[a0, b0] =
              std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MPair>(
                  m0_value.v());
          _result = (sum_md(*a0) + sum_md(*b0));
        }
      }
    } else if (std::holds_alternative<_after_sum_e_in_Add>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_in_Add>(_popped));
      _stack.pop_back();
      const LoopifyMutualPartialApp::e<uint64_t> &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_e_in_Add_2{std::move(_result)});
      _stack.emplace_back(_call{&b0});
    } else if (std::holds_alternative<_after_sum_e_in_Add_2>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_in_Add_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_sum_e_in_MConst>(_popped));
      _stack.pop_back();
      uint64_t u0 = _f.u0;
      _result = (u0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyMutualPartialApp::sum_md(
    const LoopifyMutualPartialApp::md<uint64_t> &m) {
  // Explicit stack replaces the non-tail recursion of sum_md: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualPartialApp::md<uint64_t> *m;
  };

  struct _call_sum_e_entry {
    const LoopifyMutualPartialApp::e<uint64_t> *x;
  };

  struct _after_sum_e_entry_in_Add {
    const LoopifyMutualPartialApp::e<uint64_t> *b0;
  };

  struct _after_sum_e_entry_in_Add_2 {
    uint64_t _tmp2;
  };

  struct _after_sum_e_entry_in_MConst {
    uint64_t u0;
  };

  struct _after_sum_md_in_MPair {
    const LoopifyMutualPartialApp::md<uint64_t> *b0;
  };

  struct _after_sum_md_in_MPair_2 {
    uint64_t _tmp6;
  };

  using _frame =
      std::variant<_call, _call_sum_e_entry, _after_sum_e_entry_in_Add,
                   _after_sum_e_entry_in_Add_2, _after_sum_e_entry_in_MConst,
                   _after_sum_md_in_MPair, _after_sum_md_in_MPair_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&m});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualPartialApp::md<uint64_t> &m = *_f.m;
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::md<uint64_t>::MNull>(m.v())) {
        _result = UINT64_C(0);
      } else if (
          std::holds_alternative<
              typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(m.v())) {
        const auto &[u0, x0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MConst>(
                m.v());
        _stack.emplace_back(_after_sum_e_entry_in_MConst{u0});
        _stack.emplace_back(_call_sum_e_entry{crane_raw(x0)});
      } else if (
          std::holds_alternative<
              typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(m.v())) {
        const auto &[l0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MNode>(
                m.v());
        const List<LoopifyMutualPartialApp::md<uint64_t>> &l0_value = *l0;
        _result = l0_value.template fold_left<uint64_t>(
            [](uint64_t acc,
               const LoopifyMutualPartialApp::md<uint64_t> &m0) {
              return (acc + sum_md(m0));
            },
            UINT64_C(0));
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualPartialApp::md<uint64_t>::MPair>(
                m.v());
        _stack.emplace_back(_after_sum_md_in_MPair{crane_raw(b0)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_call_sum_e_entry>(_popped)) {
      auto _f = std::move(std::get<_call_sum_e_entry>(_popped));
      _stack.pop_back();
      const LoopifyMutualPartialApp::e<uint64_t> &x = *_f.x;
      if (std::holds_alternative<
              typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(x.v())) {
        const auto &[n0] = std::get<
            typename LoopifyMutualPartialApp::e<uint64_t>::Leaf>(x.v());
        _result = std::move(n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(x.v())) {
        const auto &[u0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Tag>(x.v());
        _result = std::move(u0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualPartialApp::e<uint64_t>::Add>(x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualPartialApp::e<uint64_t>::Add>(x.v());
        _stack.emplace_back(_after_sum_e_entry_in_Add{crane_raw(b0)});
        _stack.emplace_back(_call_sum_e_entry{crane_raw(a0)});
      } else {
        const auto &[m1] = std::get<
            typename LoopifyMutualPartialApp::e<uint64_t>::Meta>(x.v());
        _stack.emplace_back(_call{crane_raw(m1)});
      }
    } else if (std::holds_alternative<_after_sum_e_entry_in_Add>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_Add>(_popped));
      _stack.pop_back();
      const LoopifyMutualPartialApp::e<uint64_t> &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_e_entry_in_Add_2{std::move(_result)});
      _stack.emplace_back(_call_sum_e_entry{&b0});
    } else if (std::holds_alternative<_after_sum_e_entry_in_Add_2>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_Add_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    } else if (std::holds_alternative<_after_sum_e_entry_in_MConst>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_MConst>(_popped));
      _stack.pop_back();
      uint64_t u0 = _f.u0;
      _result = (u0 + std::move(_result));
    } else if (std::holds_alternative<_after_sum_md_in_MPair>(_popped)) {
      auto _f = std::move(std::get<_after_sum_md_in_MPair>(_popped));
      _stack.pop_back();
      const LoopifyMutualPartialApp::md<uint64_t> &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_md_in_MPair_2{std::move(_result)});
      _stack.emplace_back(_call{&b0});
    } else {
      auto _f = std::move(std::get<_after_sum_md_in_MPair_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp6 + std::move(_result));
    }
  }
  return _result;
}

/// leaves doubled: 2*(1+2+4) = 14; tags and consts +100 each: 107 + 105 + 101 =
/// 313
bool LoopifyMutualPartialApp::check() {
  return sum_e(ft_e<LoopifyMutualPartialApp::endo_double, uint64_t, uint64_t>(
      [](uint64_t u) { return (u + UINT64_C(100)); }, sample)) ==
         (UINT64_C(14) + UINT64_C(313));
}
