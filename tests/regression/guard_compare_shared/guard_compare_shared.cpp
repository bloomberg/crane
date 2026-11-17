#include "guard_compare_shared.h"

Comparison Nat::compare(uint64_t n, uint64_t m) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_m = m;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      if (_loop_m <= 0) {
        return Comparison::EQ;
      } else {
        uint64_t _x = _loop_m - 1;
        return Comparison::LT;
      }
    } else {
      uint64_t n_ = _loop_n - 1;
      if (_loop_m <= 0) {
        return Comparison::GT;
      } else {
        uint64_t m_ = _loop_m - 1;
        _loop_m = m_;
        _loop_n = n_;
      }
    }
  }
}

Comparison GuardCompareShared::tcompare(const GuardCompareShared::tree &a,
                                        const GuardCompareShared::tree &b) {
  // Explicit stack replaces the non-tail recursion of tcompare: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const GuardCompareShared::tree *b;
    const GuardCompareShared::tree *a;
  };

  struct _after_tcompare_in_Node {
    uint64_t a1;
    const GuardCompareShared::tree *a2;
    uint64_t a10;
    const GuardCompareShared::tree *a20;
  };

  using _frame = std::variant<_call, _after_tcompare_in_Node>;
  Comparison _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&b, &a});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const GuardCompareShared::tree &b = *_f.b;
      const GuardCompareShared::tree &a = *_f.a;
      if (b.v().same_as(a.v())) {
        _result = Comparison::EQ;
      } else {
        if (crane::holds_alternative<typename GuardCompareShared::tree::Leaf>(
                a.v())) {
          if (crane::holds_alternative<typename GuardCompareShared::tree::Leaf>(
                  b.v())) {
            _result = Comparison::EQ;
          } else {
            _result = Comparison::LT;
          }
        } else {
          const auto &[a0, a1, a2] =
              crane::get<typename GuardCompareShared::tree::Node>(a.v());
          if (crane::holds_alternative<typename GuardCompareShared::tree::Leaf>(
                  b.v())) {
            _result = Comparison::GT;
          } else {
            const auto &[a00, a10, a20] =
                crane::get<typename GuardCompareShared::tree::Node>(b.v());
            _stack.emplace_back(
                _after_tcompare_in_Node{a1, crane_raw(a2), a10,
                                        crane_raw(a20)});
            _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
          }
        }
      }
    } else {
      auto _f = std::move(crane::get<_after_tcompare_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const GuardCompareShared::tree &a2 = *_f.a2;
      uint64_t a10 = _f.a10;
      const GuardCompareShared::tree &a20 = *_f.a20;
      Comparison _tmp1 = std::move(_result);
      switch (_tmp1) {
      case Comparison::EQ: {
        switch (Nat::compare(a1, a10)) {
        case Comparison::EQ: {
          _stack.emplace_back(_call{&a20, &a2});
          break;
        }
        case Comparison::LT: {
          _result = Comparison::LT;
          break;
        }
        case Comparison::GT: {
          _result = Comparison::GT;
          break;
        }
        default:
          std::unreachable();
        }
        break;
      }
      case Comparison::LT: {
        _result = Comparison::LT;
        break;
      }
      case Comparison::GT: {
        _result = Comparison::GT;
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
  return _result;
}

GuardCompareShared::tree GuardCompareShared::build(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<GuardCompareShared::tree> _root{};
  crane::shared_box<GuardCompareShared::tree> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = crane::shared_box<GuardCompareShared::tree>::make(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = typename GuardCompareShared::tree::Node(
          nullptr, _loop_n,
          crane::shared_box<GuardCompareShared::tree>::make(tree::leaf()));
      GuardCompareShared::tree &_node =
          (_write ? *(*_write =
                          crane::shared_box<GuardCompareShared::tree>::make(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &crane::get<typename GuardCompareShared::tree::Node>(_node.v_mut()).a0;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}
