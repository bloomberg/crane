#include "mem_safety_probe18.h"

uint64_t MemSafetyProbe18::sum_list(
    const MemSafetyProbe18::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe18::mylist<uint64_t> *l;
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
      const MemSafetyProbe18::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe18::mylist<uint64_t>::Mycons>(
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

/// TEST 5: Complex fold that builds a tree from a list.
MemSafetyProbe18::tree
MemSafetyProbe18::fold_left_tree(const MemSafetyProbe18::mylist<uint64_t> &l,
                                 MemSafetyProbe18::tree acc) {
  MemSafetyProbe18::tree _loop_acc = std::move(acc);
  const MemSafetyProbe18::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe18::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe18::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      _loop_acc = tree::node(std::move(_loop_acc), a0, tree::leaf());
      _loop_l = a1.get();
    }
  }
}

/// TEST 8: Nested constructor building: build a list of trees
/// using the same tree in different positions.
MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
MemSafetyProbe18::build_tree_list(MemSafetyProbe18::tree t, uint64_t n) {
  std::unique_ptr<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> _head{};
  std::unique_ptr<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> *_write =
      &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write =
          std::make_unique<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
              mylist<MemSafetyProbe18::tree>::mynil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell =
          std::make_unique<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
              typename mylist<MemSafetyProbe18::tree>::Mycons(
                  tree::node(t, _loop_n, tree::leaf()), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<MemSafetyProbe18::tree>::Mycons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t MemSafetyProbe18::sum_tree_list(
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    decltype(std::declval<MemSafetyProbe18::tree &>().tree_sum()) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_tree_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_Resume_Mycons{a0.tree_sum()});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}
