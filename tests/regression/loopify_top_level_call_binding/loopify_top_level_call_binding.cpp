#include "loopify_top_level_call_binding.h"

/// A recursive call bound at the top of a function's body, the rest of
/// the body after it.
///
/// csum's body matches nothing: it adds key c to a local fixpoint
/// applied to kids c, which Normalize binds first.  The machine adopts
/// the fixpoint, which calls back into csum, and reroutes the bound call
/// to it.  The machine rewrote its body one top-level statement at a time,
/// so the binding never resumed into the addition after it, and the
/// rerouted call was left naming the entry, which is no function.
uint64_t
LoopifyTopLevelCallBinding::key(const LoopifyTopLevelCallBinding::cell &c) {
  const auto &[key1, kids0] =
      std::get<typename LoopifyTopLevelCallBinding::cell::MkCell>(c.v());
  return key1;
}

List<LoopifyTopLevelCallBinding::cell>
LoopifyTopLevelCallBinding::kids(const LoopifyTopLevelCallBinding::cell &c) {
  const auto &[key0, kids1] =
      std::get<typename LoopifyTopLevelCallBinding::cell::MkCell>(c.v());
  return *kids1;
}

uint64_t LoopifyTopLevelCallBinding::csum(
    const LoopifyTopLevelCallBinding::cell
        &c) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    LoopifyTopLevelCallBinding::cell c;
  };

  /// CraneEnter_go: captures varying parameters for each recursive call.
  struct CraneEnter_go {
    List<LoopifyTopLevelCallBinding::cell> l;
  };

  /// CraneCont1: saves [c], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    LoopifyTopLevelCallBinding::cell c;
  };

  /// CraneCont_Cons: saves [a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    std::shared_ptr<List<LoopifyTopLevelCallBinding::cell>> a1;
  };

  /// CraneCont_Cons_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneEnter_go, CraneCont1,
                                  CraneCont_Cons, CraneCont_Cons_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{c});
  /// Loopified csum: CraneEnter -> CraneCont1 -> CraneCont_Cons ->
  /// CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyTopLevelCallBinding::cell &c = std::move(_f.c);
      uint64_t _tmp3;
      _stack.emplace_back(CraneCont1{c});
      _stack.emplace_back(CraneEnter_go{kids(c)});
    } else if (std::holds_alternative<CraneEnter_go>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_go>(_frame));
      const List<LoopifyTopLevelCallBinding::cell> &l = std::move(_f.l);
      if (std::holds_alternative<
              typename List<LoopifyTopLevelCallBinding::cell>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyTopLevelCallBinding::cell>::Cons>(
                l.v());
        _stack.emplace_back(CraneCont_Cons{a1});
        _stack.emplace_back(CraneEnter{a0});
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      const LoopifyTopLevelCallBinding::cell &c = std::move(_f.c);
      _result = (key(c) + std::move(_result));
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      std::shared_ptr<List<LoopifyTopLevelCallBinding::cell>> a1 =
          std::move(_f.a1);
      _stack.emplace_back(CraneCont_Cons_1{std::move(_result)});
      _stack.emplace_back(CraneEnter_go{*a1});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// A chain n cells deep, each holding k.
LoopifyTopLevelCallBinding::cell LoopifyTopLevelCallBinding::chain(
    uint64_t n, uint64_t k) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  LoopifyTopLevelCallBinding::cell _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified chain: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result =
            cell::mkcell(k, List<LoopifyTopLevelCallBinding::cell>::nil());
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      _result =
          cell::mkcell(k, List<LoopifyTopLevelCallBinding::cell>::cons(
                              std::move(_result),
                              List<LoopifyTopLevelCallBinding::cell>::nil()));
    }
  }
  return _result;
}
