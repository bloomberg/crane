#include "mem_safety_probe27.h"

uint64_t MemSafetyProbe27::tree_sum(
    const MemSafetyProbe27::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe27::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe27::tree *a0;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe27::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{crane_raw(a0), a1});
        _stack.emplace_back(_Enter{crane_raw(a2)});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe27::tree_depth(
    const MemSafetyProbe27::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe27::tree *t;
  };

  /// _After_Node: saves [a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe27::tree *a0;
    std::decay_t<decltype(UINT64_C(1))> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    std::decay_t<decltype(UINT64_C(1))> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_depth: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe27::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{crane_raw(a0), UINT64_C(1)});
        _stack.emplace_back(_Enter{crane_raw(a2)});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_f._s1 + std::max(std::move(_result), std::move(_f._result)));
    }
  }
  return _result;
}

std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::pair_with_fn(MemSafetyProbe27::tree t) {
  return std::make_pair([=](uint64_t x) mutable { return (x + tree_sum(t)); },
                        tree_sum(t));
}

std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::cond_pair_fn(MemSafetyProbe27::tree t, bool b) {
  if (b) {
    return std::make_pair([=](uint64_t x) mutable { return (x + tree_sum(t)); },
                          UINT64_C(1));
  } else {
    return std::make_pair(
        [=](uint64_t x) mutable { return (x + tree_depth(t)); }, UINT64_C(2));
  }
}

std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::pair_two_trees(MemSafetyProbe27::tree t1,
                                 MemSafetyProbe27::tree t2) {
  return std::make_pair(
      [=](uint64_t x) mutable { return ((x + tree_sum(t1)) + tree_sum(t2)); },
      tree_sum(t1));
}

std::optional<std::function<uint64_t(uint64_t)>>
MemSafetyProbe27::opt_tree_fn(MemSafetyProbe27::tree t, bool b) {
  if (b) {
    return std::make_optional<std::function<uint64_t(uint64_t)>>(
        [=](uint64_t x) mutable { return (x + tree_sum(t)); });
  } else {
    return std::optional<std::function<uint64_t(uint64_t)>>();
  }
}

std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::nested_closure_pair(MemSafetyProbe27::tree t) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t x) mutable {
    return (x + tree_sum(t));
  };
  return std::make_pair([=](uint64_t x) mutable { return f(f(x)); },
                        tree_sum(std::move(t)));
}

std::pair<std::pair<std::function<uint64_t(uint64_t)>,
                    std::function<uint64_t(uint64_t)>>,
          uint64_t>
MemSafetyProbe27::triple_fns(MemSafetyProbe27::tree t) {
  return std::make_pair(
      std::make_pair([=](uint64_t x) mutable { return (x + tree_sum(t)); },
                     [=](uint64_t x) mutable { return (x + tree_depth(t)); }),
      (tree_sum(t) + tree_depth(t)));
}

std::pair<std::function<uint64_t(uint64_t)>, MemSafetyProbe27::tree>
MemSafetyProbe27::fn_and_tree(MemSafetyProbe27::tree t) {
  return std::make_pair([=](uint64_t x) mutable { return (x + tree_sum(t)); },
                        t);
}

std::pair<std::optional<std::function<uint64_t(uint64_t)>>, uint64_t>
MemSafetyProbe27::wrapped_fn(MemSafetyProbe27::tree t, bool b) {
  return std::make_pair(
      (b ? std::make_optional<std::function<uint64_t(uint64_t)>>(
               [=](uint64_t x) mutable { return (x + tree_sum(t)); })
         : std::optional<std::function<uint64_t(uint64_t)>>()),
      tree_sum(t));
}
