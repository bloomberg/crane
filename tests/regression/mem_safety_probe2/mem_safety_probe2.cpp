#include "mem_safety_probe2.h"

/// TEST 7: Closure escaping through a list, then applied.
MemSafetyProbe2::mylist<uint64_t> MemSafetyProbe2::map_apply(
    const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> &fs,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> *fs;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe2::mylist<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&fs});
  /// Loopified map_apply: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> &fs =
          *_f.fs;
      if (std::holds_alternative<typename MemSafetyProbe2::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fs.v());
        _stack.emplace_back(_Resume_Mycons{a0(x)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = mylist<uint64_t>::mycons(_f.x, _result);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe2::mysum(
    const MemSafetyProbe2::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe2::mylist<uint64_t> *l;
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
  /// Loopified mysum: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe2::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe2::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(l.v());
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

/// TEST 13: Fold building tree from closures' results.
MemSafetyProbe2::tree MemSafetyProbe2::fold_tree_build(
    const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> &fs,
    uint64_t
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t acc;
    const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> *fs;
  };

  /// _Resume_Mycons: saves [_s0, acc], resumes after recursive call with
  /// _result.
  struct _Resume_Mycons {
    std::decay_t<decltype(tree::leaf())> _s0;
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe2::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, &fs});
  /// Loopified fold_tree_build: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t acc = _f.acc;
      const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> &fs =
          *_f.fs;
      if (std::holds_alternative<typename MemSafetyProbe2::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fs.v());
        _stack.emplace_back(_Resume_Mycons{tree::leaf(), a0(acc)});
        _stack.emplace_back(_Enter{a0(acc), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = tree::node(_result, _f.acc, _f._s0);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe2::apply_all(
    const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> &fs,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> *fs;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&fs});
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe2::mylist<std::function<uint64_t(uint64_t)>> &fs =
          *_f.fs;
      if (std::holds_alternative<typename MemSafetyProbe2::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fs.v());
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
