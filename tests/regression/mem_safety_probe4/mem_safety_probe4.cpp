#include "mem_safety_probe4.h"

/// TEST 1: Partial app applied to recursive result.
/// The closure f captures tree t by &, but must survive across the
/// recursive call in the loopified version.
/// f(sum_through(xs)) requires f to be stored in a continuation frame.
unsigned int MemSafetyProbe4::sum_through(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    MemSafetyProbe4::tree a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_through: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = _f.a0.sum_values(_result);
    }
  }
  return _result;
}

/// TEST 2: Recursive result + partial app result.
/// add_through(xs) + f(0): f might be pre-evaluated or stored in frame.
unsigned int MemSafetyProbe4::add_through(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified add_through: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        std::function<unsigned int(unsigned int)> f =
            [&](unsigned int _x0) -> unsigned int {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{f(0u)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

/// TEST 3: Two partial apps from same tree, used around recursive call.
unsigned int MemSafetyProbe4::double_partial(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [_s0, f], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int _s0;
    std::function<unsigned int(unsigned int)> f;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified double_partial: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        MemSafetyProbe4::mylist<MemSafetyProbe4::tree> a1_value = *a1;
        std::function<unsigned int(unsigned int)> f =
            [=](unsigned int _x0) mutable -> unsigned int {
          return a0.sum_values(_x0);
        };
        std::function<unsigned int(unsigned int)> g =
            [&](unsigned int _x0) -> unsigned int {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{g(0u), std::move(f)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.f(_result) + _f._s0);
    }
  }
  return _result;
}

unsigned int MemSafetyProbe4::weighted_sum(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l,
    unsigned int
        w) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int w;
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [w], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int w;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{w, &l});
  /// Loopified weighted_sum: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      unsigned int w = _f.w;
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        MemSafetyProbe4::mylist<MemSafetyProbe4::tree> a1_value = *a1;
        std::function<unsigned int(unsigned int)> f =
            [=](unsigned int _x0) mutable -> unsigned int {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{f(w)});
        _stack.emplace_back(_Enter{f(0u), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.w + _result);
    }
  }
  return _result;
}

/// TEST 5: Map building new trees from partial app results across recursion.
MemSafetyProbe4::mylist<unsigned int> MemSafetyProbe4::transform_list(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l) {
  std::unique_ptr<MemSafetyProbe4::mylist<unsigned int>> _head{};
  std::unique_ptr<MemSafetyProbe4::mylist<unsigned int>> *_write = &_head;
  const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
            _loop_l->v())) {
      *_write = std::make_unique<MemSafetyProbe4::mylist<unsigned int>>(
          mylist<unsigned int>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
          _loop_l->v());
      std::function<unsigned int(unsigned int)> f =
          [&](unsigned int _x0) -> unsigned int { return a0.sum_values(_x0); };
      auto _cell = std::make_unique<MemSafetyProbe4::mylist<unsigned int>>(
          typename mylist<unsigned int>::Mycons(f(0u), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename mylist<unsigned int>::Mycons>((*_write)->v_mut())
               .a1;
      _loop_l = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

unsigned int MemSafetyProbe4::mysum(
    const MemSafetyProbe4::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<unsigned int> *l;
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
  /// Loopified mysum: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe4::mylist<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe4::mylist<unsigned int>::Mycons>(
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

unsigned int MemSafetyProbe4::process_list(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [f], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<unsigned int(unsigned int)> f;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified process_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        MemSafetyProbe4::mylist<MemSafetyProbe4::tree> a1_value = *a1;
        std::function<unsigned int(unsigned int)> f =
            [=](unsigned int _x0) mutable -> unsigned int {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{std::move(f)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = apply_to(_f.f, _result);
    }
  }
  return _result;
}

/// TEST 7: Nested recursion with closure capture across calls.
unsigned int MemSafetyProbe4::nested_apply(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l,
    unsigned int base) {
  unsigned int _result;
  unsigned int _loop_base = std::move(base);
  const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
            _loop_l->v())) {
      _result = _loop_base;
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
          _loop_l->v());
      std::function<unsigned int(unsigned int)> f =
          [&](unsigned int _x0) -> unsigned int { return a0.sum_values(_x0); };
      _loop_base = f(_loop_base);
      _loop_l = a1.get();
    }
  }
  return _result;
}
