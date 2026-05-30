#include "mem_safety_probe14.h"

uint64_t MemSafetyProbe14::sum_fns(
    const MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>> *l;
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
      const MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe14::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe14::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0(UINT64_C(0))});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 5: Closure captures tree, tree is pattern-matched
/// AFTER closure creation. The match destructures the tree.
/// The closure must still hold the original tree.
uint64_t MemSafetyProbe14::capture_then_match(MemSafetyProbe14::tree t) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
    return (t.tree_sum() + n);
  };
  if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
          t.v_mut())) {
    return f(UINT64_C(0));
  } else {
    auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe14::tree::Node>(t.v_mut());
    return ((f(std::move(a1)) + a0->tree_sum()) + a2->tree_sum());
  }
}

MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe14::tree_level_fns(
    const MemSafetyProbe14::tree &t,
    uint64_t depth) { /// _Enter: captures varying parameters for each recursive
                      /// call.

  struct _Enter {
    uint64_t depth;
    const MemSafetyProbe14::tree *t;
  };

  /// _After_Node: saves [_s0, a0_value, _s2, _s3], dispatches next recursive
  /// call.
  struct _After_Node {
    uint64_t _s0;
    const MemSafetyProbe14::tree *a0_value;
    std::function<uint64_t(uint64_t)> _s2;
    std::function<uint64_t(uint64_t)> _s3;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>> _result;
    std::function<uint64_t(uint64_t)> _s1;
    std::function<uint64_t(uint64_t)> _s2;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{depth, &t});
  /// Loopified tree_level_fns: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t depth = _f.depth;
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
              t.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(_After_Node{
            (UINT64_C(1) + depth), a0.get(),
            [=](uint64_t n) mutable {
              return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
            },
            [=](uint64_t n) mutable {
              return (((depth * UINT64_C(100)) + a1) + n);
            }});
        _stack.emplace_back(_Enter{(UINT64_C(1) + depth), a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f._s2),
                                        std::move(_f._s3)});
      _stack.emplace_back(_Enter{_f._s0, _f.a0_value});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = mylist<std::function<uint64_t(uint64_t)>>::mycons(
          std::move(_f._s2),
          mylist<std::function<uint64_t(uint64_t)>>::mycons(
              std::move(_f._s1),
              std::move(_result).mylist_append(std::move(_f._result))));
    }
  }
  return _result;
}

/// TEST 8: Large tree stress test. Many closures, deep recursion.
MemSafetyProbe14::tree MemSafetyProbe14::make_balanced(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [_s0, n], resumes after recursive call with _result.
  struct _Resume_n_ {
    std::decay_t<decltype(tree::leaf())> _s0;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  MemSafetyProbe14::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_balanced: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{tree::leaf(), n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = tree::node(std::move(_result), _f.n, _f._s0);
    }
  }
  return _result;
}

MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe14::collect_closures(
    const MemSafetyProbe14::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe14::tree *t;
  };

  /// _After_Node: saves [a0_value, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe14::tree *a0_value;
    std::function<uint64_t(uint64_t)> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>> _result;
    std::function<uint64_t(uint64_t)> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe14::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified collect_closures: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
              t.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(_After_Node{
            a0.get(), [=](uint64_t n) mutable { return (a1 + n); }});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f._s1)});
      _stack.emplace_back(_Enter{_f.a0_value});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = mylist<std::function<uint64_t(uint64_t)>>::mycons(
          std::move(_f._s1),
          std::move(_result).mylist_append(std::move(_f._result)));
    }
  }
  return _result;
}
