#include "mem_safety_probe5.h"

/// TEST 1: Partial app of get_left_val, applied to recursive result.
/// The closure body accesses nested tree structure.
unsigned int MemSafetyProbe5::sum_left_vals(
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    MemSafetyProbe5::tree a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_left_vals: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = _f.a0.get_left_val(_result);
    }
  }
  return _result;
}

/// TEST 2: Build a list of partial apps from trees, then apply all.
/// Each partial app captures a tree with nested structure.
MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe5::build_getters(
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &l) {
  std::unique_ptr<
      MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  MemSafetyProbe5::mylist<MemSafetyProbe5::tree> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mynil>(
            _loop_l.v())) {
      *_write = std::make_unique<
          MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons>(
          _loop_l.v());
      const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &a1_value = *a1;
      auto _cell = std::make_unique<
          MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](unsigned int _x0) mutable -> unsigned int {
                return a0.get_left_val(_x0);
              },
              nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_head);
}

unsigned int MemSafetyProbe5::apply_all(
    const MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> &l,
    unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<unsigned int(unsigned int)> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>
          &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe5::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
        _result = std::move(x);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe5::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{std::move(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = _f.a0(_result);
    }
  }
  return _result;
}

MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe5::collect_left_vals(
    MemSafetyProbe5::tree t,
    MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> acc;
    MemSafetyProbe5::tree t;
  };

  /// _Resume_Node: saves [a0_value], resumes after recursive call with _result.
  struct _Resume_Node {
    MemSafetyProbe5::tree a0_value;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, t});
  /// Loopified collect_left_vals: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> acc =
          std::move(_f.acc);
      MemSafetyProbe5::tree t = std::move(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe5::tree::Leaf>(
              t.v_mut())) {
        _result = std::move(acc);
      } else {
        auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe5::tree::Node>(t.v_mut());
        const MemSafetyProbe5::tree &a0_value = *a0;
        const MemSafetyProbe5::tree &a2_value = *a2;
        _stack.emplace_back(_Resume_Node{a0_value});
        _stack.emplace_back(
            _Enter{mylist<std::function<unsigned int(unsigned int)>>::mycons(
                       [=](unsigned int _x0) mutable -> unsigned int {
                         return t.get_left_val(_x0);
                       },
                       std::move(acc)),
                   a2_value});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _stack.emplace_back(_Enter{std::move(_result), std::move(_f.a0_value)});
    }
  }
  return _result;
}

/// TEST 6: Stress test with very large list of trees.
MemSafetyProbe5::mylist<MemSafetyProbe5::tree>
MemSafetyProbe5::make_tree_list(unsigned int n) {
  std::unique_ptr<MemSafetyProbe5::mylist<MemSafetyProbe5::tree>> _head{};
  std::unique_ptr<MemSafetyProbe5::mylist<MemSafetyProbe5::tree>> *_write =
      &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write =
          std::make_unique<MemSafetyProbe5::mylist<MemSafetyProbe5::tree>>(
              mylist<MemSafetyProbe5::tree>::mynil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell =
          std::make_unique<MemSafetyProbe5::mylist<MemSafetyProbe5::tree>>(
              typename mylist<MemSafetyProbe5::tree>::Mycons(
                  tree::node(tree::node(tree::leaf(), _loop_n, tree::leaf()),
                             (_loop_n * 2u), tree::leaf()),
                  nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<MemSafetyProbe5::tree>::Mycons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

unsigned int MemSafetyProbe5::sum_getters(
    const MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> &l,
    unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>> *l;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_getters: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe5::mylist<std::function<unsigned int(unsigned int)>>
          &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe5::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe5::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0(x)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.x + _result);
    }
  }
  return _result;
}
