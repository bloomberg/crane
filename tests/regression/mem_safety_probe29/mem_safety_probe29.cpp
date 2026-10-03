#include "mem_safety_probe29.h"

/// TEST 2: Dup pattern — use inner tree twice in outer construction.
MemSafetyProbe29::outer
MemSafetyProbe29::dup_inner(const MemSafetyProbe29::inner &i) {
  return outer::onode(outer::onode(outer::oleaf(), i, outer::oleaf()), i,
                      outer::onode(outer::oleaf(), i, outer::oleaf()));
}

/// TEST 5: Deep 3-child tree to stress clone/destructor.
MemSafetyProbe29::tree3 MemSafetyProbe29::build_tree3(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: saves [n, n_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_n_ {
    uint64_t n;
    uint64_t n_;
  };

  /// _Cont_n__1: saves [_tmp3, n, n_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_n__1 {
    MemSafetyProbe29::tree3 _tmp3;
    uint64_t n;
    uint64_t n_;
  };

  /// _Cont_n__2: saves [_tmp2, _tmp3, n], resumes after recursive call, then
  /// processes rest.
  struct _Cont_n__2 {
    MemSafetyProbe29::tree3 _tmp2;
    MemSafetyProbe29::tree3 _tmp3;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont_n_, _Cont_n__1, _Cont_n__2>;
  MemSafetyProbe29::tree3 _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified build_tree3: _Enter -> _Cont_n_ -> _Cont_n__1 -> _Cont_n__2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree3::t3leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n, n_});
        _stack.emplace_back(_Enter{n_});
      }
    } else if (std::holds_alternative<_Cont_n_>(_frame)) {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_Cont_n__1{std::move(_result), n, n_});
      _stack.emplace_back(_Enter{n_});
    } else if (std::holds_alternative<_Cont_n__1>(_frame)) {
      auto _f = std::move(std::get<_Cont_n__1>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(
          _Cont_n__2{std::move(_result), std::move(_f._tmp3), n});
      _stack.emplace_back(_Enter{n_});
    } else {
      auto _f = std::move(std::get<_Cont_n__2>(_frame));
      uint64_t n = _f.n;
      _result = tree3::t3node(std::move(_f._tmp3), std::move(_f._tmp2),
                              std::move(_result), n);
    }
  }
  return _result;
}
