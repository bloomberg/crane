#include "mem_safety_probe5.h"

/// TEST 1: Partial app of get_left_val, applied to recursive result.
/// The closure body accesses nested tree structure.
uint64_t MemSafetyProbe5::sum_left_vals(
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
  uint64_t _result{};
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
        _result = UINT64_C(0);
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
MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe5::build_getters(
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified build_getters: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mynil>(
              l.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons>(
            l.v());
        const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &a1_value = *a1;
        _stack.emplace_back(
            _Resume_Mycons{[=](uint64_t _x0) mutable -> uint64_t {
              return a0.get_left_val(_x0);
            }});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result =
          mylist<std::function<uint64_t(uint64_t)>>::mycons(_f._s0, _result);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe5::apply_all(
    const MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> &l,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe5::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = std::move(x);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe5::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
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

MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe5::collect_left_vals(
    MemSafetyProbe5::tree t,
    MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>>
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> acc;
    MemSafetyProbe5::tree t;
  };

  /// _Resume_Node: saves [a0_value], resumes after recursive call with _result.
  struct _Resume_Node {
    MemSafetyProbe5::tree a0_value;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(acc), std::move(t)});
  /// Loopified collect_left_vals: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> acc =
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
            _Enter{mylist<std::function<uint64_t(uint64_t)>>::mycons(
                       [=](uint64_t _x0) mutable -> uint64_t {
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
MemSafetyProbe5::mylist<MemSafetyProbe5::tree> MemSafetyProbe5::make_tree_list(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [_s0], resumes after recursive call with _result.
  struct _Resume_n_ {
    std::decay_t<decltype(tree::node(
        tree::node(tree::leaf(), std::declval<uint64_t &>(), tree::leaf()),
        (std::declval<uint64_t &>() * UINT64_C(2)), tree::leaf()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  MemSafetyProbe5::mylist<MemSafetyProbe5::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_tree_list: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = mylist<MemSafetyProbe5::tree>::mynil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(
            _Resume_n_{tree::node(tree::node(tree::leaf(), n, tree::leaf()),
                                  (n * UINT64_C(2)), tree::leaf())});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = mylist<MemSafetyProbe5::tree>::mycons(_f._s0, _result);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe5::sum_getters(
    const MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> &l,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> *l;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_getters: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe5::mylist<std::function<uint64_t(uint64_t)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe5::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe5::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
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
