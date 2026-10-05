#include "loopify_decltype.h"

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
uint64_t LoopifyDecltype::count_true(
    const List<bool> &xs) { /// CraneEnter: captures varying parameters for each
                            /// recursive call.

  struct CraneEnter {
    const List<bool> *xs;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    bool a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&xs});
  /// Loopified count_true: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<bool> &xs = *_f.xs;
      if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      bool a0 = _f.a0;
      _result = ((a0 ? UINT64_C(1) : UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyDecltype::sum_flagged(const List<LoopifyDecltype::item>
                                 &xs) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const List<LoopifyDecltype::item> *xs;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    LoopifyDecltype::item a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&xs});
  /// Loopified sum_flagged: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<LoopifyDecltype::item> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyDecltype::item>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyDecltype::item>::Cons>(xs.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      LoopifyDecltype::item a0 = std::move(_f.a0);
      _result =
          ((a0.item_flag ? a0.item_val : UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}
