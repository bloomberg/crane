#include "mem_safety_probe13.h"

unsigned int MemSafetyProbe13::sum_list(
    const MemSafetyProbe13::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::mylist<unsigned int> *l;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::mylist<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe13::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename MemSafetyProbe13::mylist<unsigned int>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

/// TEST 1: Double-recursion on tree where both subtrees
/// are used in closures AND in recursive calls.
/// Tests if the flatten optimization moves unique_ptr fields
/// that are also captured by closures.
std::pair<MemSafetyProbe13::mylist<unsigned int>,
          MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>>
MemSafetyProbe13::tree_vals_and_fns(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _Cont_Node: saves [d_a0_value, d_a1, d_a2_value], resumes after recursive
  /// call, then processes rest.
  struct _Cont_Node {
    MemSafetyProbe13::tree d_a0_value;
    unsigned int d_a1;
    const MemSafetyProbe13::tree *d_a2_value;
  };

  /// _Cont_lvals: saves [d_a0_value, d_a1, d_a2_value, lfns, lvals], resumes
  /// after recursive call, then processes rest.
  struct _Cont_lvals {
    MemSafetyProbe13::tree d_a0_value;
    unsigned int d_a1;
    MemSafetyProbe13::tree d_a2_value;
    MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>> lfns;
    MemSafetyProbe13::mylist<unsigned int> lvals;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_lvals>;
  std::pair<MemSafetyProbe13::mylist<unsigned int>,
            MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>>
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
        _result = std::make_pair(
            mylist<unsigned int>::mynil(),
            mylist<std::function<unsigned int(unsigned int)>>::mynil());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        MemSafetyProbe13::tree d_a0_value = *d_a0;
        MemSafetyProbe13::tree d_a2_value = *d_a2;
        _stack.emplace_back(_Cont_Node{d_a0_value, d_a1, d_a2.get()});
        _stack.emplace_back(_Enter{d_a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      MemSafetyProbe13::tree d_a0_value = std::move(_f.d_a0_value);
      unsigned int d_a1 = _f.d_a1;
      const MemSafetyProbe13::tree &d_a2_value = *_f.d_a2_value;
      const MemSafetyProbe13::mylist<unsigned int> &lvals = _result.first;
      const MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>
          &lfns = _result.second;
      _stack.emplace_back(
          _Cont_lvals{d_a0_value, d_a1, d_a2_value, lfns, lvals});
      _stack.emplace_back(_Enter{&d_a2_value});
    } else {
      auto _f = std::move(std::get<_Cont_lvals>(_frame));
      MemSafetyProbe13::tree d_a0_value = std::move(_f.d_a0_value);
      unsigned int d_a1 = _f.d_a1;
      MemSafetyProbe13::tree d_a2_value = std::move(_f.d_a2_value);
      MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>> lfns =
          std::move(_f.lfns);
      MemSafetyProbe13::mylist<unsigned int> lvals = std::move(_f.lvals);
      const MemSafetyProbe13::mylist<unsigned int> &rvals = _result.first;
      const MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>
          &rfns = _result.second;
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int n) mutable {
            return ((d_a0_value.tree_sum() + d_a2_value.tree_sum()) + n);
          };
      _result = std::make_pair(
          mylist<unsigned int>::mycons(d_a1, lvals.app(rvals)),
          mylist<std::function<unsigned int(unsigned int)>>::mycons(
              f, lfns.app(rfns)));
    }
  }
  return _result;
}

/// TEST 4: Deeply nested tree with closures at EVERY level.
/// Each closure captures values from its level AND from the parent.
/// Tests stack depth and closure lifetime with deep nesting.
MemSafetyProbe13::tree MemSafetyProbe13::make_deep(unsigned int n) {
  std::unique_ptr<MemSafetyProbe13::tree> _head{};
  std::unique_ptr<MemSafetyProbe13::tree> *_write = &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<MemSafetyProbe13::tree>(tree::leaf());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<MemSafetyProbe13::tree>(typename tree::Node(
          nullptr, _loop_n,
          std::make_unique<MemSafetyProbe13::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write = &std::get<typename tree::Node>((*_write)->v_mut()).d_a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe13::depth_fns(const MemSafetyProbe13::tree &t,
                            unsigned int parent_val) {
  std::unique_ptr<
      MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  unsigned int _loop_parent_val = std::move(parent_val);
  MemSafetyProbe13::tree _loop_t = t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
            _loop_t.v())) {
      *_write = std::make_unique<
          MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename MemSafetyProbe13::tree::Node>(_loop_t.v());
      MemSafetyProbe13::tree d_a0_value = *d_a0;
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int n) mutable {
            return ((_loop_parent_val + d_a1) + n);
          };
      auto _cell = std::make_unique<
          MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              f, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_parent_val = d_a1;
      _loop_t = d_a0_value;
      continue;
    }
  }
  return std::move(*_head);
}

MemSafetyProbe13::ftree MemSafetyProbe13::tree_to_ftree(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _After_Node: saves [d_a0_value, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe13::tree *d_a0_value;
    std::function<unsigned int(unsigned int)> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe13::ftree _result;
    std::function<unsigned int(unsigned int)> _s1;
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
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        MemSafetyProbe13::tree d_a0_value = *d_a0;
        MemSafetyProbe13::tree d_a2_value = *d_a2;
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
      _result = ftree::fnode(_result, _f._s1, _f._result);
    }
  }
  return _result;
}

/// TEST 6: Flatten a tree of lists into a single list,
/// where each list element is a closure.
MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe13::flatten_tree_fns(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _After_Node: saves [d_a0_value, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe13::tree *d_a0_value;
    std::function<unsigned int(unsigned int)> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>> _result;
    std::function<unsigned int(unsigned int)> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe13::mylist<std::function<unsigned int(unsigned int)>> _result{};
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
        _result = mylist<std::function<unsigned int(unsigned int)>>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        MemSafetyProbe13::tree d_a0_value = *d_a0;
        MemSafetyProbe13::tree d_a2_value = *d_a2;
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
      _result =
          _result.app(mylist<std::function<unsigned int(unsigned int)>>::mycons(
              _f._s1, _f._result));
    }
  }
  return _result;
}
