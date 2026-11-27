#include "loopify_recursor_instantiated.h"

/// A recursor of a type-indexed family, loopified and instantiated.
///
/// expr_rect reads its recursive calls through a coercion, at the motive
/// of the index each constructor fixes.  Normalize left them in place,
/// ordinary C++ calls inside the machine, and a call left there names no
/// instantiation: the recursor's C++ spells its motive T1 only in its
/// result type, nothing deduces it (wip/recursor_self_call_no_motive), and
/// size did not compile.  Each is now bound at the motive, which the
/// recursor's C++ spells, and the machine resumes after it: a succE chain
/// a hundred thousand deep runs in one machine.
uint64_t
LoopifyRecursorInstantiated::size(const LoopifyRecursorInstantiated::expr &e) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyRecursorInstantiated::expr *e;
  };

  struct _after_size_in_FstE {};

  struct _after_size_in_Ite {
    const LoopifyRecursorInstantiated::expr *a1;
    const LoopifyRecursorInstantiated::expr *a2;
  };

  struct _after_size_in_Ite_2 {
    const LoopifyRecursorInstantiated::expr *a2;
    uint64_t _tmp4;
  };

  struct _after_size_in_Ite_3 {
    uint64_t _tmp4;
    uint64_t _tmp3;
  };

  struct _after_size_in_PairE {
    const LoopifyRecursorInstantiated::expr *b;
  };

  struct _after_size_in_PairE_2 {
    uint64_t _tmp6;
  };

  struct _after_size_in_SuccE {};

  using _frame = std::variant<_call, _after_size_in_FstE, _after_size_in_Ite,
                              _after_size_in_Ite_2, _after_size_in_Ite_3,
                              _after_size_in_PairE, _after_size_in_PairE_2,
                              _after_size_in_SuccE>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&e});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyRecursorInstantiated::expr &e = *_f.e;
      if (std::holds_alternative<
              typename LoopifyRecursorInstantiated::expr::SuccE>(e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyRecursorInstantiated::expr::SuccE>(e.v());
        _stack.emplace_back(_after_size_in_SuccE{});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else if (std::holds_alternative<
                     typename LoopifyRecursorInstantiated::expr::Ite>(e.v())) {
        const auto &[a, a1, a2] =
            std::get<typename LoopifyRecursorInstantiated::expr::Ite>(e.v());
        _stack.emplace_back(_after_size_in_Ite{crane_raw(a1), crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else if (std::holds_alternative<
                     typename LoopifyRecursorInstantiated::expr::PairE>(e.v())) {
        const auto &[a, b] =
            std::get<typename LoopifyRecursorInstantiated::expr::PairE>(e.v());
        _stack.emplace_back(_after_size_in_PairE{crane_raw(b)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else if (std::holds_alternative<
                     typename LoopifyRecursorInstantiated::expr::FstE>(e.v())) {
        const auto &[a] =
            std::get<typename LoopifyRecursorInstantiated::expr::FstE>(e.v());
        _stack.emplace_back(_after_size_in_FstE{});
        _stack.emplace_back(_call{crane_raw(a)});
      } else {
        _result = UINT64_C(1);
      }
    } else if (std::holds_alternative<_after_size_in_FstE>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_FstE>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    } else if (std::holds_alternative<_after_size_in_Ite>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Ite>(_popped));
      _stack.pop_back();
      const LoopifyRecursorInstantiated::expr &a1 = *_f.a1;
      const LoopifyRecursorInstantiated::expr &a2 = *_f.a2;
      _stack.emplace_back(_after_size_in_Ite_2{&a2, _result});
      _stack.emplace_back(_call{&a1});
    } else if (std::holds_alternative<_after_size_in_Ite_2>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Ite_2>(_popped));
      _stack.pop_back();
      const LoopifyRecursorInstantiated::expr &a2 = *_f.a2;
      _stack.emplace_back(_after_size_in_Ite_3{_f._tmp4, _result});
      _stack.emplace_back(_call{&a2});
    } else if (std::holds_alternative<_after_size_in_Ite_3>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Ite_3>(_popped));
      _stack.pop_back();
      _result = ((_f._tmp4 + _f._tmp3 + _result) + 1);
    } else if (std::holds_alternative<_after_size_in_PairE>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_PairE>(_popped));
      _stack.pop_back();
      const LoopifyRecursorInstantiated::expr &b = *_f.b;
      _stack.emplace_back(_after_size_in_PairE_2{_result});
      _stack.emplace_back(_call{&b});
    } else if (std::holds_alternative<_after_size_in_PairE_2>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_PairE_2>(_popped));
      _stack.pop_back();
      _result = ((_f._tmp6 + _result) + 1);
    } else {
      auto _f = std::move(std::get<_after_size_in_SuccE>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}
