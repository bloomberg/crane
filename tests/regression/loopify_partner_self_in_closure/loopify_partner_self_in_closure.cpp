#include "loopify_partner_self_in_closure.h"

/// sum_e calls its partner sum_md as an operand, and sum_md calls
/// sum_e back, so sum_e's machine would enter a copy of sum_md -- but
/// sum_md also calls itself inside the closure it folds a list with, and
/// the copy a machine enters is no value a closure could call.  Its body
/// runs in place of the call instead.
uint64_t
LoopifyPartnerSelfInClosure::sum_e(const LoopifyPartnerSelfInClosure::e &x) {
  // Explicit stack replaces the non-tail recursion of sum_e: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPartnerSelfInClosure::e *x;
  };

  struct _after_sum_e_in_MConst {};

  using _frame = std::variant<_call, _after_sum_e_in_MConst>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const LoopifyPartnerSelfInClosure::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyPartnerSelfInClosure::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyPartnerSelfInClosure::e::Leaf>(x.v());
        _result = std::move(n0);
      } else {
        const auto &[m0] =
            std::get<typename LoopifyPartnerSelfInClosure::e::Meta>(x.v());
        const LoopifyPartnerSelfInClosure::md &m0_value = *m0;
        if (std::holds_alternative<
                typename LoopifyPartnerSelfInClosure::md::MNil>(m0_value.v())) {
          _result = (UINT64_C(1) + UINT64_C(0));
        } else if (
            std::holds_alternative<
                typename LoopifyPartnerSelfInClosure::md::MNode>(m0_value.v())) {
          const auto &[l0] =
              std::get<typename LoopifyPartnerSelfInClosure::md::MNode>(
                  m0_value.v());
          const List<LoopifyPartnerSelfInClosure::md> &l0_value = *l0;
          _result =
              (UINT64_C(1) + l0_value.template fold_left<uint64_t>(
                                 [](uint64_t acc,
                                    const LoopifyPartnerSelfInClosure::md &m1) {
                                   return (acc + sum_md(m1));
                                 },
                                 UINT64_C(0)));
        } else {
          const auto &[x1] =
              std::get<typename LoopifyPartnerSelfInClosure::md::MConst>(
                  m0_value.v());
          _stack.emplace_back(_after_sum_e_in_MConst{});
          _stack.emplace_back(_call{crane_raw(x1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_sum_e_in_MConst>(_popped));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyPartnerSelfInClosure::sum_md(const LoopifyPartnerSelfInClosure::md &m) {
  // Explicit stack replaces the non-tail recursion of sum_md: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPartnerSelfInClosure::md *m;
  };

  struct _after_sum_md_in_Meta {};

  using _frame = std::variant<_call, _after_sum_md_in_Meta>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&m});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const LoopifyPartnerSelfInClosure::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyPartnerSelfInClosure::md::MNil>(
              m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyPartnerSelfInClosure::md::MNode>(m.v())) {
        const auto &[l0] =
            std::get<typename LoopifyPartnerSelfInClosure::md::MNode>(m.v());
        const List<LoopifyPartnerSelfInClosure::md> &l0_value = *l0;
        _result = l0_value.template fold_left<uint64_t>(
            [](uint64_t acc,
               const LoopifyPartnerSelfInClosure::md &m0) {
              return (acc + sum_md(m0));
            },
            UINT64_C(0));
      } else {
        const auto &[x0] =
            std::get<typename LoopifyPartnerSelfInClosure::md::MConst>(m.v());
        auto &&_sv0 = *x0;
        if (std::holds_alternative<
                typename LoopifyPartnerSelfInClosure::e::Leaf>(_sv0.v())) {
          const auto &[n0] =
              std::get<typename LoopifyPartnerSelfInClosure::e::Leaf>(_sv0.v());
          _result = std::move(n0);
        } else {
          const auto &[m1] =
              std::get<typename LoopifyPartnerSelfInClosure::e::Meta>(_sv0.v());
          _stack.emplace_back(_after_sum_md_in_Meta{});
          _stack.emplace_back(_call{crane_raw(m1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_sum_md_in_Meta>(_popped));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

/// 1 + (2 + (1 + 3))
bool LoopifyPartnerSelfInClosure::check() {
  return sum_e(e::meta(md::mnode(List<LoopifyPartnerSelfInClosure::md>::cons(
      md::mconst(e::leaf(UINT64_C(2))), List<LoopifyPartnerSelfInClosure::md>::cons(
                                            md::mconst(e::meta(md::mconst(
                                                e::leaf(UINT64_C(3))))),
                                            List<
                                                LoopifyPartnerSelfInClosure::md>::cons(
                                                md::mnil(),
                                                List<
                                                    LoopifyPartnerSelfInClosure::md>::nil())))))) ==
         UINT64_C(7);
}
