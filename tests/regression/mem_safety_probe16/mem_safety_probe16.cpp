#include "mem_safety_probe16.h"

uint64_t MemSafetyProbe16::sum_list(
    const MemSafetyProbe16::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe16::mylist<uint64_t> *l;
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
      const MemSafetyProbe16::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe16::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(
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

MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe16::build_summers(
    const MemSafetyProbe16::mylist<MemSafetyProbe16::tree>
        &trees) { /// _Enter: captures varying parameters for each recursive
                  /// call.

  struct _Enter {
    const MemSafetyProbe16::mylist<MemSafetyProbe16::tree> *trees;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&trees});
  /// Loopified build_summers: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe16::mylist<MemSafetyProbe16::tree> &trees = *_f.trees;
      if (std::holds_alternative<
              typename MemSafetyProbe16::mylist<MemSafetyProbe16::tree>::Mynil>(
              trees.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe16::mylist<MemSafetyProbe16::tree>::Mycons>(
            trees.v());
        const MemSafetyProbe16::mylist<MemSafetyProbe16::tree> &a1_value = *a1;
        _stack.emplace_back(
            _Resume_Mycons{[=](uint64_t _x0) mutable -> uint64_t {
              return a0.make_summer(_x0);
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

uint64_t MemSafetyProbe16::apply_fns(
    const MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> *fns;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&fns});
  /// Loopified apply_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe16::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe16::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
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

/// TEST 3: Build a list of closures where each closure captures
/// the SAME tree at different levels.
/// Tests whether the tree is properly cloned for each closure.
MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe16::multi_capture_tree(
    MemSafetyProbe16::tree t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [_s0], resumes after recursive call with _result.
  struct _Resume_n_ {
    std::function<uint64_t(uint64_t)> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified multi_capture_tree: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{
            [=](uint64_t x) mutable { return ((t.tree_sum() + x) + n); }});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result =
          mylist<std::function<uint64_t(uint64_t)>>::mycons(_f._s0, _result);
    }
  }
  return _result;
}

/// TEST 4: Return a closure from inside a NESTED match.
/// The closure captures bindings from BOTH match levels.
uint64_t MemSafetyProbe16::nested_match_closure(
    const MemSafetyProbe16::tree &t,
    const MemSafetyProbe16::mylist<uint64_t> &l, uint64_t n) {
  if (std::holds_alternative<typename MemSafetyProbe16::tree::Leaf>(t.v())) {
    return n;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe16::tree::Node>(t.v());
    if (std::holds_alternative<
            typename MemSafetyProbe16::mylist<uint64_t>::Mynil>(l.v())) {
      return (a1 + n);
    } else {
      const auto &[a00, a10] =
          std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(l.v());
      return ((((a0->tree_sum() + a2->tree_sum()) + a1) + a00) + n);
    }
  }
}

/// TEST 7: Map + apply pattern: build closures from tree children,
/// apply them to values from another list.
MemSafetyProbe16::mylist<uint64_t> MemSafetyProbe16::zip_apply(
    const MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> &fns,
    const MemSafetyProbe16::mylist<uint64_t> &
        vals) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe16::mylist<uint64_t> *vals;
    const MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> *fns;
  };

  /// _Resume_Mycons: saves [a00], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe16::mylist<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&vals, &fns});
  /// Loopified zip_apply: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe16::mylist<uint64_t> &vals = *_f.vals;
      const MemSafetyProbe16::mylist<std::function<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe16::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe16::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
        if (std::holds_alternative<
                typename MemSafetyProbe16::mylist<uint64_t>::Mynil>(vals.v())) {
          _result = mylist<uint64_t>::mynil();
        } else {
          const auto &[a00, a10] =
              std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(
                  vals.v());
          _stack.emplace_back(_Resume_Mycons{a0(a00)});
          _stack.emplace_back(_Enter{a10.get(), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = mylist<uint64_t>::mycons(_f.a00, _result);
    }
  }
  return _result;
}

MemSafetyProbe16::mylist<uint64_t>
MemSafetyProbe16::flatten_cps(const MemSafetyProbe16::tree &t) {
  return flatten_cps_aux(
      t, [](MemSafetyProbe16::mylist<uint64_t> x) { return x; });
}
