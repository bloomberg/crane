#include "mem_safety_probe14.h"

unsigned int MemSafetyProbe14::sum_fns(
    const MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>>
        *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>>
          &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe14::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe14::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0(0u)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// TEST 5: Closure captures tree, tree is pattern-matched
/// AFTER closure creation. The match destructures the tree.
/// The closure must still hold the original tree.
unsigned int MemSafetyProbe14::capture_then_match(MemSafetyProbe14::tree t) {
  std::function<unsigned int(unsigned int)> f = [=](unsigned int n) mutable {
    return (t.tree_sum() + n);
  };
  if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
          t.v_mut())) {
    return f(0u);
  } else {
    auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe14::tree::Node>(t.v_mut());
    return ((f(std::move(d_a1)) + (*d_a0).tree_sum()) + (*d_a2).tree_sum());
  }
}

MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe14::tree_level_fns(
    const MemSafetyProbe14::tree &t,
    unsigned int depth) { /// _Enter: captures varying parameters for each
                          /// recursive call.

  struct _Enter {
    unsigned int depth;
    const MemSafetyProbe14::tree *t;
  };

  /// _After_Node: saves [_s0, d_a0_value, _s2, _s3], dispatches next recursive
  /// call.
  struct _After_Node {
    unsigned int _s0;
    const MemSafetyProbe14::tree *d_a0_value;
    std::function<unsigned int(unsigned int)> _s2;
    std::function<unsigned int(unsigned int)> _s3;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>> _result;
    std::function<unsigned int(unsigned int)> _s1;
    std::function<unsigned int(unsigned int)> _s2;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{depth, &t});
  /// Loopified tree_level_fns: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      unsigned int depth = _f.depth;
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
              t.v())) {
        _result = mylist<std::function<unsigned int(unsigned int)>>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        MemSafetyProbe14::tree d_a0_value = *d_a0;
        MemSafetyProbe14::tree d_a2_value = *d_a2;
        _stack.emplace_back(_After_Node{
            (1u + depth), d_a0.get(),
            [=](unsigned int n) mutable {
              return ((d_a0_value.tree_sum() + d_a2_value.tree_sum()) + n);
            },
            [=](unsigned int n) mutable {
              return (((depth * 100u) + d_a1) + n);
            }});
        _stack.emplace_back(_Enter{(1u + depth), d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f._s2),
                                        std::move(_f._s3)});
      _stack.emplace_back(_Enter{_f._s0, _f.d_a0_value});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = mylist<std::function<unsigned int(unsigned int)>>::mycons(
          _f._s2, mylist<std::function<unsigned int(unsigned int)>>::mycons(
                      _f._s1, _result.mylist_append(_f._result)));
    }
  }
  return _result;
}

/// TEST 8: Large tree stress test. Many closures, deep recursion.
MemSafetyProbe14::tree MemSafetyProbe14::make_balanced(unsigned int n) {
  std::unique_ptr<MemSafetyProbe14::tree> _head{};
  std::unique_ptr<MemSafetyProbe14::tree> *_write = &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<MemSafetyProbe14::tree>(tree::leaf());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<MemSafetyProbe14::tree>(typename tree::Node(
          nullptr, _loop_n,
          std::make_unique<MemSafetyProbe14::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write = &std::get<typename tree::Node>((*_write)->v_mut()).d_a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe14::collect_closures(
    const MemSafetyProbe14::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe14::tree *t;
  };

  /// _After_Node: saves [d_a0_value, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe14::tree *d_a0_value;
    std::function<unsigned int(unsigned int)> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>> _result;
    std::function<unsigned int(unsigned int)> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe14::mylist<std::function<unsigned int(unsigned int)>> _result{};
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
        _result = mylist<std::function<unsigned int(unsigned int)>>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        MemSafetyProbe14::tree d_a0_value = *d_a0;
        MemSafetyProbe14::tree d_a2_value = *d_a2;
        _stack.emplace_back(_After_Node{
            d_a0.get(), [=](unsigned int n) mutable { return (d_a1 + n); }});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f._s1)});
      _stack.emplace_back(_Enter{_f.d_a0_value});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = mylist<std::function<unsigned int(unsigned int)>>::mycons(
          _f._s1, _result.mylist_append(_f._result));
    }
  }
  return _result;
}
