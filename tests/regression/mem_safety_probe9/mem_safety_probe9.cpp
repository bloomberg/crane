#include "mem_safety_probe9.h"

uint64_t MemSafetyProbe9::sum_fns(
    const MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe9::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe9::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0(UINT64_C(0))});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// TEST 1: Collect closures that each capture a subtree.
/// Both l and r are captured AND used in recursive calls.
MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe9::collect_subtree_sums(
    const MemSafetyProbe9::tree &t,
    MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>>
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> acc;
    const MemSafetyProbe9::tree *t;
  };

  /// _Resume_Node: saves [a0_value], resumes after recursive call with _result.
  struct _Resume_Node {
    const MemSafetyProbe9::tree *a0_value;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, &t});
  /// Loopified collect_subtree_sums: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> acc =
          std::move(_f.acc);
      const MemSafetyProbe9::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe9::tree::Leaf>(t.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe9::tree::Node>(t.v());
        const MemSafetyProbe9::tree &a0_value = *a0;
        const MemSafetyProbe9::tree &a2_value = *a2;
        _stack.emplace_back(_Resume_Node{a0.get()});
        _stack.emplace_back(
            _Enter{mylist<std::function<uint64_t(uint64_t)>>::mycons(
                       [=](auto _xarg0) mutable {
                         return _collect_subtree_sums_f(_xarg0, a0_value, a1,
                                                        a2_value);
                       },
                       std::move(acc)),
                   a2.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _stack.emplace_back(_Enter{std::move(_result), _f.a0_value});
    }
  }
  return _result;
}

/// TEST 2: Similar but each closure captures ONLY the left subtree.
/// The left subtree is shared between closure and recursive call.
MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe9::collect_left_sums(
    const MemSafetyProbe9::tree &t,
    MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>>
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> acc;
    const MemSafetyProbe9::tree *t;
  };

  /// _Resume_Node: saves [a0_value], resumes after recursive call with _result.
  struct _Resume_Node {
    const MemSafetyProbe9::tree *a0_value;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, &t});
  /// Loopified collect_left_sums: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> acc =
          std::move(_f.acc);
      const MemSafetyProbe9::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe9::tree::Leaf>(t.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe9::tree::Node>(t.v());
        const MemSafetyProbe9::tree &a0_value = *a0;
        const MemSafetyProbe9::tree &a2_value = *a2;
        _stack.emplace_back(_Resume_Node{a0.get()});
        _stack.emplace_back(
            _Enter{mylist<std::function<uint64_t(uint64_t)>>::mycons(
                       [=](auto _xarg0) mutable {
                         return _collect_left_sums_f(_xarg0, a0_value);
                       },
                       std::move(acc)),
                   a2.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _stack.emplace_back(_Enter{std::move(_result), _f.a0_value});
    }
  }
  return _result;
}

/// TEST 3: Build closures from list where each closure
/// captures the tail and a computed value.
MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe9::list_accum_closures(
    const MemSafetyProbe9::mylist<uint64_t> &l,
    MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> acc) {
  MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> _result;
  MemSafetyProbe9::mylist<std::function<uint64_t(uint64_t)>> _loop_acc =
      std::move(acc);
  MemSafetyProbe9::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe9::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      _result = std::move(_loop_acc);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe9::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe9::mylist<uint64_t> &a1_value = *a1;
      uint64_t tail_len = a1_value.length();
      _loop_acc = mylist<std::function<uint64_t(uint64_t)>>::mycons(
          [=](auto _xarg0) mutable {
            return _list_accum_closures_f(_xarg0, a0, tail_len);
          },
          std::move(_loop_acc));
      _loop_l = a1_value;
    }
  }
  return _result;
}

/// TEST 6: Stress test — large tree, many closures.
MemSafetyProbe9::tree MemSafetyProbe9::make_balanced(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_n_: saves [n_, n], dispatches next recursive call.
  struct _After_n_ {
    uint64_t n_;
    uint64_t n;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe9::tree _result;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _After_n_, _Combine_n_>;
  MemSafetyProbe9::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_balanced: _Enter -> _After_n_ -> _Combine_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_After_n_{n_, n});
        _stack.emplace_back(_Enter{n_});
      }
    } else if (std::holds_alternative<_After_n_>(_frame)) {
      auto _f = std::move(std::get<_After_n_>(_frame));
      _stack.emplace_back(_Combine_n_{std::move(_result), _f.n});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = tree::node(_result, _f.n, _f._result);
    }
  }
  return _result;
}
