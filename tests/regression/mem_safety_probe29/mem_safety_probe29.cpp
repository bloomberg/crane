#include "mem_safety_probe29.h"

/// TEST 2: Dup pattern — use inner tree twice in outer construction.
MemSafetyProbe29::outer MemSafetyProbe29::dup_inner(MemSafetyProbe29::inner i) {
  return outer::onode(outer::onode(outer::oleaf(), i, outer::oleaf()), i,
                      outer::onode(outer::oleaf(), i, outer::oleaf()));
}

/// TEST 5: Deep 3-child tree to stress clone/destructor.
MemSafetyProbe29::tree3 MemSafetyProbe29::build_tree3(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _After_n_: saves [n__0, n__1, n], dispatches next recursive call.
  struct _After_n_ {
    unsigned int n__0;
    unsigned int n__1;
    unsigned int n;
  };

  /// _After_n__1: saves [_result, n_, n], dispatches next recursive call.
  struct _After_n__1 {
    MemSafetyProbe29::tree3 _result;
    unsigned int n_;
    unsigned int n;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe29::tree3 _result_0;
    MemSafetyProbe29::tree3 _result_1;
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _After_n_, _After_n__1, _Combine_n_>;
  MemSafetyProbe29::tree3 _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(n));
  /// Loopified build_tree3: _Enter -> _After_n_ -> _After_n__1 -> _Combine_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = tree3::t3leaf();
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_After_n_(n_, n_, n));
        _stack.emplace_back(_Enter(n_));
      }
    } else if (std::holds_alternative<_After_n_>(_frame)) {
      auto _f = std::move(std::get<_After_n_>(_frame));
      _stack.emplace_back(_After_n__1(std::move(_result), _f.n__1, _f.n));
      _stack.emplace_back(_Enter(_f.n__0));
    } else if (std::holds_alternative<_After_n__1>(_frame)) {
      auto _f = std::move(std::get<_After_n__1>(_frame));
      _stack.emplace_back(
          _Combine_n_(std::move(_f._result), std::move(_result), _f.n));
      _stack.emplace_back(_Enter(_f.n_));
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = tree3::t3node(_result, _f._result_1, _f._result_0, _f.n);
    }
  }
  return _result;
}
