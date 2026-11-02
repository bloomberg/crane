#include "loopify_partner_back_under_fixpoint.h"

/// tree_size's partner forest_size calls it back only from a local
/// fixpoint over a list of trees, and tree_size calls forest_size as
/// the operand of an addition.  No machine can enter forest_size, so its
/// body is spliced in place of the call.  The addition is then copied into
/// the one branch of the match the body is, which applies the local
/// fixpoint where tree_size's machine runs it as a loop of its own: the
/// calls of tree_size in it are turns, and a chain of any depth runs in
/// one C++ frame.
uint64_t LoopifyPartnerBackUnderFixpoint::tree_size(
    const LoopifyPartnerBackUnderFixpoint::tree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    LoopifyPartnerBackUnderFixpoint::tree t;
  };

  /// CraneEnter_sizes: captures varying parameters for each recursive call.
  struct CraneEnter_sizes {
    List<LoopifyPartnerBackUnderFixpoint::tree> l;
  };

  /// CraneCont_Cons: saves [a11], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    std::shared_ptr<List<LoopifyPartnerBackUnderFixpoint::tree>> a11;
  };

  /// CraneCont_Cons_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    uint64_t _tmp2;
  };

  /// CraneCont_Forest0: saves [n0], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Forest0 {
    uint64_t n0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneEnter_sizes, CraneCont_Cons,
                                  CraneCont_Cons_1, CraneCont_Forest0>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{t});
  /// Loopified tree_size: CraneEnter -> CraneCont_Cons -> CraneCont_Cons_1 ->
  /// CraneCont_Forest0.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyPartnerBackUnderFixpoint::tree &t = std::move(_f.t);
      const auto &[n0, kids0] =
          std::get<typename LoopifyPartnerBackUnderFixpoint::tree::Node>(t.v());
      auto &&_sv0 = *kids0;
      const auto &[ts0] =
          std::get<typename LoopifyPartnerBackUnderFixpoint::forest::Forest0>(
              _sv0.v());
      _stack.emplace_back(CraneCont_Forest0{n0});
      _stack.emplace_back(CraneEnter_sizes{*ts0});
    } else if (std::holds_alternative<CraneEnter_sizes>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_sizes>(_frame));
      const List<LoopifyPartnerBackUnderFixpoint::tree> &l = std::move(_f.l);
      if (std::holds_alternative<
              typename List<LoopifyPartnerBackUnderFixpoint::tree>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a01, a11] = std::get<
            typename List<LoopifyPartnerBackUnderFixpoint::tree>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a11});
        _stack.emplace_back(CraneEnter{a01});
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      std::shared_ptr<List<LoopifyPartnerBackUnderFixpoint::tree>> a11 =
          std::move(_f.a11);
      _stack.emplace_back(CraneCont_Cons_1{std::move(_result)});
      _stack.emplace_back(CraneEnter_sizes{*a11});
    } else if (std::holds_alternative<CraneCont_Cons_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_Forest0>(_frame));
      uint64_t n0 = _f.n0;
      _result = (n0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyPartnerBackUnderFixpoint::forest_size(
    const LoopifyPartnerBackUnderFixpoint::forest &f) {
  const auto &[ts0] =
      std::get<typename LoopifyPartnerBackUnderFixpoint::forest::Forest0>(
          f.v());
  auto sizes =
      [&](const List<LoopifyPartnerBackUnderFixpoint::tree> &l) -> uint64_t {
    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<LoopifyPartnerBackUnderFixpoint::tree> *l;
    };
    /// CraneCont_Cons: saves [_tmp2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      uint64_t _tmp2;
    };
    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified sizes: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<LoopifyPartnerBackUnderFixpoint::tree> &l = *_f.l;
        if (std::holds_alternative<
                typename List<LoopifyPartnerBackUnderFixpoint::tree>::Nil>(
                l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a00, a10] = std::get<
              typename List<LoopifyPartnerBackUnderFixpoint::tree>::Cons>(
              l.v());
          _stack.emplace_back(CraneCont_Cons{tree_size(a00)});
          _stack.emplace_back(CraneEnter{crane_raw(a10)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (_f._tmp2 + std::move(_result));
      }
    }
    return _result;
  };
  return sizes(*ts0);
}

LoopifyPartnerBackUnderFixpoint::tree LoopifyPartnerBackUnderFixpoint::chain(
    uint64_t k, LoopifyPartnerBackUnderFixpoint::tree t) {
  LoopifyPartnerBackUnderFixpoint::tree _loop_t = std::move(t);
  uint64_t _loop_k = k;
  while (true) {
    if (_loop_k <= 0) {
      return _loop_t;
    } else {
      uint64_t k_ = _loop_k - 1;
      _loop_t = tree::node(
          UINT64_C(1),
          forest::forest0(List<LoopifyPartnerBackUnderFixpoint::tree>::cons(
              std::move(_loop_t),
              List<LoopifyPartnerBackUnderFixpoint::tree>::cons(
                  tree::node(
                      UINT64_C(1),
                      forest::forest0(
                          List<LoopifyPartnerBackUnderFixpoint::tree>::nil())),
                  List<LoopifyPartnerBackUnderFixpoint::tree>::nil()))));
      _loop_k = k_;
    }
  }
}
