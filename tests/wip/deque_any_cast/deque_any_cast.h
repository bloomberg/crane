#ifndef INCLUDED_DEQUE_ANY_CAST
#define INCLUDED_DEQUE_ANY_CAST

#include <any>
#include <concepts>
#include <deque>
#include <utility>
#include <variant>
#include <vector>

template <typename I>concept Monoid = requires (typename I::m_carrier a0,
typename I::m_carrier a1) {
  typename I::m_carrier;
  { I::m_op(a0,
a1) } -> std::convertible_to<typename I::m_carrier>;
} && (requires {
  { I::m_id() } -> std::convertible_to<typename I::m_carrier>;
} || requires {
  { I::m_id } -> std::convertible_to<typename I::m_carrier>;
});

struct DequeAnyCast {
  using m_carrier = std::any;

  struct nat_monoid {
    using m_carrier = uint64_t;

    static uint64_t m_op(uint64_t a0, uint64_t a1) { return (a0 + a1); }

    static uint64_t m_id() { return UINT64_C(0); }
  };

  static_assert(Monoid<nat_monoid>);

  template <Monoid _tcI0>
  static typename _tcI0::m_carrier mfold(
      const std::deque<typename _tcI0::m_carrier>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      std::deque<typename _tcI0::m_carrier> l;
    };

    /// _Resume_x: saves [x], resumes after recursive call with _result.
    struct _Resume_x {
      typename _tcI0::m_carrier x;
    };

    using _Frame = std::variant<_Enter, _Resume_x>;
    typename _tcI0::m_carrier _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l});
    /// Loopified mfold: _Enter -> _Resume_x.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const std::deque<typename _tcI0::m_carrier> &l = std::move(_f.l);
        if (l.empty()) {
          _result = _tcI0::m_id();
        } else {
          const auto &x = l.front();
          std::decay_t<decltype(l)> rest(l.begin() + 1, l.end());
          _stack.emplace_back(_Resume_x{x});
          _stack.emplace_back(_Enter{rest});
        }
      } else {
        auto _f = std::move(std::get<_Resume_x>(_frame));
        _result = _tcI0::m_op(std::move(_f.x), std::move(_result));
      }
    }
    return _result;
  }

  static inline const uint64_t test_fold_add =
      std::any_cast<uint64_t>(mfold<nat_monoid>([](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(std::any(UINT64_C(1)), [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(std::any(UINT64_C(2)), [](auto _a0, auto _a1) {
          _a1.push_front(_a0);
          return _a1;
        }(std::any(UINT64_C(3)), std::deque<std::any>{})))));
};

#endif // INCLUDED_DEQUE_ANY_CAST
