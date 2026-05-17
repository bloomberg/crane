#include "mem_safety_probe24.h"

unsigned int MemSafetyProbe24::sum_list(
    const MemSafetyProbe24::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe24::mylist<unsigned int> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int a0;
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
      const MemSafetyProbe24::mylist<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe24::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe24::mylist<unsigned int>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

MemSafetyProbe24::mylist<unsigned int> MemSafetyProbe24::tree_to_list(
    const MemSafetyProbe24::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe24::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe24::tree *a0;
    unsigned int a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe24::mylist<unsigned int> _result;
    unsigned int a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe24::mylist<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_to_list: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe24::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
              t.v())) {
        _result = mylist<unsigned int>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe24::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = _result.app(mylist<unsigned int>::mycons(_f.a1, _f._result));
    }
  }
  return _result;
}

/// TEST 7: Build a tree from a list, using accumulated state.
/// Tests interaction between list recursion and tree construction.
MemSafetyProbe24::tree
MemSafetyProbe24::list_to_tree(const MemSafetyProbe24::mylist<unsigned int> &l,
                               MemSafetyProbe24::tree acc) {
  MemSafetyProbe24::tree _result;
  MemSafetyProbe24::tree _loop_acc = std::move(acc);
  const MemSafetyProbe24::mylist<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe24::mylist<unsigned int>::Mynil>(
            _loop_l->v())) {
      _result = std::move(_loop_acc);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe24::mylist<unsigned int>::Mycons>(
              _loop_l->v());
      _loop_acc = tree::node(std::move(_loop_acc), a0, tree::leaf());
      _loop_l = a1.get();
    }
  }
  return _result;
}

/// TEST 8: Zip two trees, producing a list of pairs.
/// Both trees are destructured simultaneously.
MemSafetyProbe24::mylist<std::pair<unsigned int, unsigned int>>
MemSafetyProbe24::zip_trees(
    const MemSafetyProbe24::tree &t1,
    const MemSafetyProbe24::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe24::tree *t2;
    const MemSafetyProbe24::tree *t1;
  };

  /// _After_Node: saves [a00, a0, _s2], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe24::tree *a00;
    const MemSafetyProbe24::tree *a0;
    decltype(std::make_pair(std::declval<unsigned int &>(),
                            std::declval<unsigned int &>())) _s2;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe24::mylist<std::pair<unsigned int, unsigned int>> _result;
    decltype(std::make_pair(std::declval<unsigned int &>(),
                            std::declval<unsigned int &>())) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe24::mylist<std::pair<unsigned int, unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t2, &t1});
  /// Loopified zip_trees: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe24::tree &t2 = *_f.t2;
      const MemSafetyProbe24::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
              t1.v())) {
        _result = mylist<std::pair<unsigned int, unsigned int>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe24::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
                t2.v())) {
          _result = mylist<std::pair<unsigned int, unsigned int>>::mynil();
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe24::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{a00.get(), a0.get(), std::make_pair(a1, a10)});
          _stack.emplace_back(_Enter{a20.get(), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
      _stack.emplace_back(_Enter{_f.a00, _f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result =
          _result.app(mylist<std::pair<unsigned int, unsigned int>>::mycons(
              _f._s1, _f._result));
    }
  }
  return _result;
}
