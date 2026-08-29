#include "mem_safety_probe4.h"

uint64_t MemSafetyProbe4::sum_through(
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
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
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
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = std::move(_f.a0).sum_values(std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::add_through(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
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
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{f(UINT64_C(0))});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (std::move(_result) + _f._s0);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::double_partial(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [_s0, f], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t _s0;
    std::function<uint64_t(uint64_t)> f;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
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
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &a1_value = *a1;
        std::function<uint64_t(uint64_t)> f =
            [=](uint64_t _x0) mutable -> uint64_t {
          return a0.sum_values(_x0);
        };
        std::function<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{g(UINT64_C(0)), std::move(f)});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (std::move(_f.f)(std::move(_result)) + _f._s0);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::weighted_sum(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l,
    uint64_t
        w) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t w;
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [w], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t w;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{w, &l});
  /// Loopified weighted_sum: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t w = _f.w;
      const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &a1_value = *a1;
        std::function<uint64_t(uint64_t)> f =
            [=](uint64_t _x0) mutable -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{f(w)});
        _stack.emplace_back(_Enter{f(UINT64_C(0)), crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.w + std::move(_result));
    }
  }
  return _result;
}

MemSafetyProbe4::mylist<uint64_t> MemSafetyProbe4::transform_list(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l) {
  std::shared_ptr<MemSafetyProbe4::mylist<uint64_t>> _head{};
  std::shared_ptr<MemSafetyProbe4::mylist<uint64_t>> *_write = &_head;
  const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
            _loop_l->v())) {
      *_write = std::make_shared<MemSafetyProbe4::mylist<uint64_t>>(
          mylist<uint64_t>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
          _loop_l->v());
      std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return a0.sum_values(_x0);
      };
      auto _cell = std::make_shared<MemSafetyProbe4::mylist<uint64_t>>(
          typename mylist<uint64_t>::Mycons(f(UINT64_C(0)), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename mylist<uint64_t>::Mycons>((*_write)->v_mut()).a1;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t MemSafetyProbe4::mysum(
    const MemSafetyProbe4::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified mysum: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe4::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe4::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe4::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::process_list(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *l;
  };

  /// _Resume_Mycons: saves [f], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> f;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
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
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
            l.v());
        const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &a1_value = *a1;
        std::function<uint64_t(uint64_t)> f =
            [=](uint64_t _x0) mutable -> uint64_t {
          return a0.sum_values(_x0);
        };
        _stack.emplace_back(_Resume_Mycons{std::move(f)});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = apply_to(std::move(_f.f), std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe4::nested_apply(
    const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> &l, uint64_t base) {
  uint64_t _loop_base = std::move(base);
  const MemSafetyProbe4::mylist<MemSafetyProbe4::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mynil>(
            _loop_l->v())) {
      return _loop_base;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe4::mylist<MemSafetyProbe4::tree>::Mycons>(
          _loop_l->v());
      std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return a0.sum_values(_x0);
      };
      _loop_base = f(_loop_base);
      _loop_l = crane_raw(a1);
    }
  }
}
