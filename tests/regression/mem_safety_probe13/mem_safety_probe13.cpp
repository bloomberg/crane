#include "mem_safety_probe13.h"

uint64_t MemSafetyProbe13::sum_list(
    const MemSafetyProbe13::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe13::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe13::mylist<uint64_t>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Double-recursion on tree where both subtrees
/// are used in closures AND in recursive calls.
/// Tests if the flatten optimization moves unique_ptr fields
/// that are also captured by closures.
std::pair<MemSafetyProbe13::mylist<uint64_t>,
          MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>>>
MemSafetyProbe13::tree_vals_and_fns(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _Cont_Node: saves [a0_value, a1, a2_value], resumes after recursive call,
  /// then processes rest.
  struct _Cont_Node {
    MemSafetyProbe13::tree a0_value;
    uint64_t a1;
    const MemSafetyProbe13::tree *a2_value;
  };

  /// _Cont_lvals: saves [a0_value, a1, a2_value, lfns, lvals], resumes after
  /// recursive call, then processes rest.
  struct _Cont_lvals {
    MemSafetyProbe13::tree a0_value;
    uint64_t a1;
    const MemSafetyProbe13::tree *a2_value;
    MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> lfns;
    MemSafetyProbe13::mylist<uint64_t> lvals;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_lvals>;
  std::pair<MemSafetyProbe13::mylist<uint64_t>,
            MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_vals_and_fns: _Enter -> _Cont_Node -> _Cont_lvals.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result =
            std::make_pair(mylist<uint64_t>::mynil(),
                           mylist<std::function<uint64_t(uint64_t)>>::mynil());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(_Cont_Node{a0_value, a1, a2.get()});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      const MemSafetyProbe13::tree &a0_value = std::move(_f.a0_value);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe13::tree &a2_value = *_f.a2_value;
      auto _cs = std::move(_result);
      MemSafetyProbe13::mylist<uint64_t> lvals = std::move(_cs.first);
      MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> lfns =
          std::move(_cs.second);
      _stack.emplace_back(_Cont_lvals{a0_value, a1, &a2_value, lfns, lvals});
      _stack.emplace_back(_Enter{&a2_value});
    } else {
      auto _f = std::move(std::get<_Cont_lvals>(_frame));
      const MemSafetyProbe13::tree &a0_value = std::move(_f.a0_value);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe13::tree &a2_value = *_f.a2_value;
      MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> lfns =
          std::move(_f.lfns);
      MemSafetyProbe13::mylist<uint64_t> lvals = std::move(_f.lvals);
      auto _cs1 = std::move(_result);
      MemSafetyProbe13::mylist<uint64_t> rvals = std::move(_cs1.first);
      MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> rfns =
          std::move(_cs1.second);
      std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
        return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
      };
      _result = std::make_pair(
          mylist<uint64_t>::mycons(a1, std::move(lvals).app(std::move(rvals))),
          mylist<std::function<uint64_t(uint64_t)>>::mycons(
              f, std::move(lfns).app(std::move(rfns))));
    }
  }
  return _result;
}

/// TEST 4: Deeply nested tree with closures at EVERY level.
/// Each closure captures values from its level AND from the parent.
/// Tests stack depth and closure lifetime with deep nesting.
MemSafetyProbe13::tree MemSafetyProbe13::make_deep(
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
  MemSafetyProbe13::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_deep: _Enter -> _Resume_n_.
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

MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe13::depth_fns(
    const MemSafetyProbe13::tree &t,
    uint64_t parent_val) { /// _Enter: captures varying parameters for each
                           /// recursive call.

  struct _Enter {
    uint64_t parent_val;
    const MemSafetyProbe13::tree *t;
  };

  /// _Resume_Node: saves [f], resumes after recursive call with _result.
  struct _Resume_Node {
    std::function<uint64_t(uint64_t)> f;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{parent_val, &t});
  /// Loopified depth_fns: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t parent_val = _f.parent_val;
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
          return ((parent_val + a1) + n);
        };
        _stack.emplace_back(_Resume_Node{std::move(f)});
        _stack.emplace_back(_Enter{a1, a0.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _result = mylist<std::function<uint64_t(uint64_t)>>::mycons(
          std::move(_f.f), std::move(_result));
    }
  }
  return _result;
}

MemSafetyProbe13::ftree MemSafetyProbe13::tree_to_ftree(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _After_Node: saves [a0_value, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe13::tree *a0_value;
    std::function<uint64_t(uint64_t)> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe13::ftree _result;
    std::function<uint64_t(uint64_t)> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe13::ftree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_to_ftree: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result = ftree::fleaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
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
      _result = ftree::fnode(std::move(_result), std::move(_f._s1),
                             std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 6: Flatten a tree of lists into a single list,
/// where each list element is a closure.
MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe13::flatten_tree_fns(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _After_Node: saves [a0_value, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe13::tree *a0_value;
    std::function<uint64_t(uint64_t)> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> _result;
    std::function<uint64_t(uint64_t)> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe13::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified flatten_tree_fns: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
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
      _result = std::move(_result).app(
          mylist<std::function<uint64_t(uint64_t)>>::mycons(
              std::move(_f._s1), std::move(_f._result)));
    }
  }
  return _result;
}
