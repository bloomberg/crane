#include "mem_safety_probe18.h"

unsigned int MemSafetyProbe18::sum_list(
    const MemSafetyProbe18::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe18::mylist<unsigned int> *l;
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
      const MemSafetyProbe18::mylist<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename MemSafetyProbe18::mylist<unsigned int>::Mycons>(
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

/// TEST 5: Complex fold that builds a tree from a list.
MemSafetyProbe18::tree MemSafetyProbe18::fold_left_tree(
    const MemSafetyProbe18::mylist<unsigned int> &l,
    MemSafetyProbe18::tree acc) {
  MemSafetyProbe18::tree _result;
  MemSafetyProbe18::tree _loop_acc = std::move(acc);
  const MemSafetyProbe18::mylist<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe18::mylist<unsigned int>::Mynil>(
            _loop_l->v())) {
      _result = std::move(_loop_acc);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MemSafetyProbe18::mylist<unsigned int>::Mycons>(
              _loop_l->v());
      _loop_acc = tree::node(std::move(_loop_acc), d_a0, tree::leaf());
      _loop_l = d_a1.get();
    }
  }
  return _result;
}

/// TEST 8: Nested constructor building: build a list of trees
/// using the same tree in different positions.
MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
MemSafetyProbe18::build_tree_list(MemSafetyProbe18::tree t,
                                  const unsigned int n) {
  std::unique_ptr<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> _head{};
  std::unique_ptr<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> *_write =
      &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
              mylist<MemSafetyProbe18::tree>::mynil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell =
          std::make_unique<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
              typename mylist<MemSafetyProbe18::tree>::Mycons(
                  tree::node(t, _loop_n, tree::leaf()), nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename mylist<MemSafetyProbe18::tree>::Mycons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}

unsigned int MemSafetyProbe18::sum_tree_list(
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> *l;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    decltype(std::declval<MemSafetyProbe18::tree &>().tree_sum()) d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_tree_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &l = *(_f.l);
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<
            typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0.tree_sum()});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}
