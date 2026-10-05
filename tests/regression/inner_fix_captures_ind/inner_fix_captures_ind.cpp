#include "inner_fix_captures_ind.h"

uint64_t InnerFixCapturesInd::len(
    const InnerFixCapturesInd::lst &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const InnerFixCapturesInd::lst *l;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified len: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const InnerFixCapturesInd::lst &l = *_f.l;
      if (std::holds_alternative<typename InnerFixCapturesInd::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename InnerFixCapturesInd::lst::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t InnerFixCapturesInd::outer(
    const InnerFixCapturesInd::lst &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const InnerFixCapturesInd::lst *l;
  };

  /// CraneCont_Cons: saves [a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    std::shared_ptr<InnerFixCapturesInd::lst> a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified outer: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const InnerFixCapturesInd::lst &l = *_f.l;
      if (std::holds_alternative<typename InnerFixCapturesInd::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename InnerFixCapturesInd::lst::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a1});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      std::shared_ptr<InnerFixCapturesInd::lst> a1 = std::move(_f.a1);
      _result = ([&]() {
        auto inner = [&](const InnerFixCapturesInd::lst &m,
                         uint64_t a) -> uint64_t {
          uint64_t _loop_a = std::move(a);
          const InnerFixCapturesInd::lst *_loop_m = &m;
          while (true) {
            if (std::holds_alternative<typename InnerFixCapturesInd::lst::Nil>(
                    _loop_m->v())) {
              return _loop_a;
            } else {
              const auto &[a2, a3] =
                  std::get<typename InnerFixCapturesInd::lst::Cons>(
                      _loop_m->v());
              _loop_a = (_loop_a + len(*a1));
              _loop_m = crane_raw(a3);
            }
          }
        };
        return inner(*a1, UINT64_C(0));
      }() + std::move(_result));
    }
  }
  return _result;
}

InnerFixCapturesInd::lst InnerFixCapturesInd::mk(uint64_t n) {
  std::optional<InnerFixCapturesInd::lst> _root{};
  std::shared_ptr<InnerFixCapturesInd::lst> *_write = nullptr;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      auto _value = lst::nil();
      (_write ? *(*_write = std::make_shared<InnerFixCapturesInd::lst>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell =
          typename InnerFixCapturesInd::lst::Cons(UINT64_C(1), nullptr);
      InnerFixCapturesInd::lst &_node =
          (_write ? *(*_write = std::make_shared<InnerFixCapturesInd::lst>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename InnerFixCapturesInd::lst::Cons>(_node.v_mut()).a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t InnerFixCapturesInd::go(uint64_t n) { return outer(mk(n)); }
