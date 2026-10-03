#include "mutual_loopify_acc.h"

uint64_t MutualLoopifyAcc::tsum(
    uint64_t acc,
    const MutualLoopifyAcc::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MutualLoopifyAcc::tree *t;
    uint64_t acc;
  };

  /// _Cont_Fcons: saves [_inl_a1], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Fcons {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_1: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_1 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_2: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_2 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_3: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_3 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_4: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_4 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_5: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_5 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_6: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_6 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_7: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_7 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  /// _Cont_Fcons_8: saves [_inl_a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Fcons_8 {
    std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Fcons, _Cont_Fcons_1, _Cont_Fcons_2,
                              _Cont_Fcons_3, _Cont_Fcons_4, _Cont_Fcons_5,
                              _Cont_Fcons_6, _Cont_Fcons_7, _Cont_Fcons_8>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t, acc});
  /// Loopified tsum: _Enter -> _Cont_Fcons -> _Cont_Fcons_1 -> _Cont_Fcons_2 ->
  /// _Cont_Fcons_3 -> _Cont_Fcons_4 -> _Cont_Fcons_5 -> _Cont_Fcons_6 ->
  /// _Cont_Fcons_7 -> _Cont_Fcons_8.
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
          _stack.emplace_back(_Cont_Fcons{_inl_a1});
          _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
        }
      }
    } else if (std::holds_alternative<_Cont_Fcons>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_1{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_1>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_2{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_2>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_2>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_3{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_3>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_3>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_4{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_4>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_4>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_5{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_5>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_5>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_6{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_6>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_6>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_7{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else if (std::holds_alternative<_Cont_Fcons_7>(_frame)) {
      auto _f = std::move(std::get<_Cont_Fcons_7>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      const MutualLoopifyAcc::forest &_inl_f = *_inl_a1;
      uint64_t _inl_acc = _inl__tmp1;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              _inl_f.v())) {
        _result = std::move(_inl_acc);
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(_inl_f.v());
        _stack.emplace_back(_Cont_Fcons_8{_inl_a1});
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Fcons_8>(_frame));
      std::shared_ptr<MutualLoopifyAcc::forest> _inl_a1 = std::move(_f._inl_a1);
      uint64_t _inl__tmp1 = std::move(_result);
      _result = fsum(_inl__tmp1, *_inl_a1);
    }
  }
  return _result;
}

uint64_t MutualLoopifyAcc::fsum(
    uint64_t acc,
    const MutualLoopifyAcc::forest
        &f) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MutualLoopifyAcc::forest *f;
    uint64_t acc;
  };

  /// _Enter_inl: captures varying parameters for each recursive call.
  struct _Enter_inl {
    MutualLoopifyAcc::tree _inl_t;
    uint64_t _inl_acc;
  };

  /// _Cont_Fcons: saves [a1], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Fcons {
    const MutualLoopifyAcc::forest *a1;
  };

  using _Frame = std::variant<_Enter, _Enter_inl, _Cont_Fcons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&f, acc});
  /// Loopified fsum: _Enter -> _Cont_Fcons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MutualLoopifyAcc::forest &f = *_f.f;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename MutualLoopifyAcc::forest::Fnil>(
              f.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1] =
            std::get<typename MutualLoopifyAcc::forest::Fcons>(f.v());
        _stack.emplace_back(_Cont_Fcons{crane_raw(a1)});
        _stack.emplace_back(_Enter_inl{*a0, acc});
      }
    } else if (std::holds_alternative<_Enter_inl>(_frame)) {
      auto _f = std::move(std::get<_Enter_inl>(_frame));
      const MutualLoopifyAcc::tree &_inl_t = std::move(_f._inl_t);
      uint64_t _inl_acc = _f._inl_acc;
      if (std::holds_alternative<typename MutualLoopifyAcc::tree::Leaf>(
              _inl_t.v())) {
        const auto &[_inl_a0] =
            std::get<typename MutualLoopifyAcc::tree::Leaf>(_inl_t.v());
        _result = (_inl_acc + _inl_a0);
      } else {
        const auto &[_inl_a0] =
            std::get<typename MutualLoopifyAcc::tree::Node>(_inl_t.v());
        _stack.emplace_back(_Enter{crane_raw(_inl_a0), _inl_acc});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Fcons>(_frame));
      const MutualLoopifyAcc::forest &a1 = *_f.a1;
      _stack.emplace_back(_Enter{&a1, std::move(_result)});
    }
  }
  return _result;
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
