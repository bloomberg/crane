#include "mutual_loopify_acc.h"

uint64_t MutualLoopifyAcc::tsum(
    uint64_t acc,
    const MutualLoopifyAcc::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MutualLoopifyAcc::tree *t;
    uint64_t acc;
  };

  /// _Cont_Fcons: saves [_inl_f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Fcons {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_1: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_1 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_2: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_2 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_3: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_3 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_4: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_4 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_5: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_5 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_6: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_6 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Cont_Fcons_7: saves [_inl_f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_7 {
    MutualLoopifyAcc::forest _inl_f;
  };

  /// _Resume_Fcons: saves [_inl_a1], resumes after recursive call with _result.
  struct _Resume_Fcons {
    MutualLoopifyAcc::forest _inl_a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Fcons, _Cont_Fcons_1, _Cont_Fcons_2,
                              _Cont_Fcons_3, _Cont_Fcons_4, _Cont_Fcons_5,
                              _Cont_Fcons_6, _Cont_Fcons_7, _Resume_Fcons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t, acc});
  /// Loopified tsum: _Enter -> _Cont_Fcons -> _Cont_Fcons_1 -> _Cont_Fcons_2 ->
  /// _Cont_Fcons_3 -> _Cont_Fcons_4 -> _Cont_Fcons_5 -> _Cont_Fcons_6 ->
  /// _Cont_Fcons_7 -> _Resume_Fcons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MutualLoopifyAcc::tree &t = *_f.t;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename MutualLoopifyAcc::tree::Leaf>(
              t.v())) {
        const auto &[a0] =
            std::get<typename MutualLoopifyAcc::tree::Leaf>(t.v());
        _result = (acc + a0);
      } else {
        const auto &[a0] =
            std::get<typename MutualLoopifyAcc::tree::Node>(t.v());
        const MutualLoopifyAcc::forest &_inl_f = *a0;
        uint64_t _inl_acc = acc;
        if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
                _inl_f.v())) {
          _result = std::move(_inl_acc);
        } else {
          const auto &[_inl_a0, _inl_a1] =
              std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
          const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
          _stack.emplace_back(_Cont_Fcons{_inl_f});
          _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
        }
      }
    } else if (std::holds_alternative<_Cont_Fcons>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_1{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_1>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_2{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_2>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_2>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_3{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_3>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_3>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_4{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_4>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_4>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_5{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_5>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_5>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_6{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_6>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_6>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
        _stack.emplace_back(_Cont_Fcons_7{_inl_f});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_7>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_7>(_frame));
      const MutualLoopifyAcc::forest &_inl_f = std::move(_f._inl_f);
      uint64_t _inl_acc = std::move(_result);
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Resume_Fcons{*_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Fcons>(_frame));
      _result = fsum(std::move(_result), std::move(_f._inl_a1));
    }
  }
  return _result;
}

uint64_t MutualLoopifyAcc::fsum(uint64_t acc,
                                const MutualLoopifyAcc::forest &f) {
  const MutualLoopifyAcc::forest *_loop_f = &f;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
            _loop_f->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MutualLoopifyAcc::forest::Fcons>(_loop_f->v());
      _loop_f = crane_raw(a1);
      _loop_acc = tsum(_loop_acc, *a0);
    }
  }
}

MutualLoopifyAcc::tree MutualLoopifyAcc::chain(uint64_t n,
                                               MutualLoopifyAcc::tree acc) {
  MutualLoopifyAcc::tree _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      _loop_acc = tree::node(forest::fcons(
          std::move(_loop_acc),
          forest::fcons(tree::leaf(UINT64_C(1)), forest::fnil())));
      _loop_n = m;
    }
  }
}

uint64_t MutualLoopifyAcc::go(uint64_t n) {
  return tsum(UINT64_C(0), chain(n, tree::leaf(UINT64_C(0))));
}
