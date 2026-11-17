#include "mem_safety_probe29.h"

/// TEST 2: Dup pattern — use inner tree twice in outer construction.
MemSafetyProbe29::outer
MemSafetyProbe29::dup_inner(const MemSafetyProbe29::inner &i) {
  return outer::onode(outer::onode(outer::oleaf(), i, outer::oleaf()), i,
                      outer::onode(outer::oleaf(), i, outer::oleaf()));
}

/// TEST 5: Deep 3-child tree to stress clone/destructor.
MemSafetyProbe29::tree3 MemSafetyProbe29::build_tree3(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of build_tree3: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_build_tree3_in_S {
    uint64_t n;
    uint64_t n_;
  };

  struct _after_build_tree3_in_S_2 {
    uint64_t n;
    uint64_t n_;
    MemSafetyProbe29::tree3 _tmp3;
  };

  struct _after_build_tree3_in_S_3 {
    uint64_t n;
    MemSafetyProbe29::tree3 _tmp3;
    MemSafetyProbe29::tree3 _tmp2;
  };

  using _frame =
      std::variant<_call, _after_build_tree3_in_S, _after_build_tree3_in_S_2,
                   _after_build_tree3_in_S_3>;
  MemSafetyProbe29::tree3 _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree3::t3leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_build_tree3_in_S{n, n_});
        _stack.emplace_back(_call{n_});
      }
    } else if (std::holds_alternative<_after_build_tree3_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_build_tree3_in_S>(_popped));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_build_tree3_in_S_2{n, n_, std::move(_result)});
      _stack.emplace_back(_call{n_});
    } else if (std::holds_alternative<_after_build_tree3_in_S_2>(_popped)) {
      auto _f = std::move(std::get<_after_build_tree3_in_S_2>(_popped));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(
          _after_build_tree3_in_S_3{n, std::move(_f._tmp3),
                                    std::move(_result)});
      _stack.emplace_back(_call{n_});
    } else {
      auto _f = std::move(std::get<_after_build_tree3_in_S_3>(_popped));
      uint64_t n = _f.n;
      _result = tree3::t3node(std::move(_f._tmp3), std::move(_f._tmp2),
                              std::move(_result), n);
    }
  }
  return _result;
}
