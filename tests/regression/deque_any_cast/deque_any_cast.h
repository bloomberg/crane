#pragma once

#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <deque>
#include <utility>
#include <variant>

template <typename I>
concept Monoid = requires {
  typename I::m_carrier;
  {
    I::m_op(std::declval<typename I::m_carrier>(),
            std::declval<typename I::m_carrier>())
  } -> std::convertible_to<typename I::m_carrier>;
} && (requires {
  {
    I::m_id()
  }
  -> std::convertible_to<typename I::m_carrier>;
} || requires {
  {
    I::m_id
  }
  -> std::convertible_to<typename I::m_carrier>;
});

struct DequeAnyCast {
  using m_carrier = crane::obj;

  struct nat_monoid {
    using m_carrier = uint64_t;

    constexpr static uint64_t m_op(uint64_t a0, uint64_t a1) {
      return (a0 + a1);
    }

    constexpr static uint64_t m_id() { return UINT64_C(0); }
  };

  static_assert(Monoid<nat_monoid>);

  template <Monoid _tcI0>
  static typename _tcI0::m_carrier
  mfold(const std::deque<typename _tcI0::m_carrier> &l) {
    // Explicit stack replaces the non-tail recursion of mfold: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      std::deque<typename _tcI0::m_carrier> l;
    };

    struct _after_mfold_in_cons {
      typename _tcI0::m_carrier x;
    };

    using _frame = std::variant<_call, _after_mfold_in_cons>;
    typename _tcI0::m_carrier _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const std::deque<typename _tcI0::m_carrier> &l = _f.l;
        if (l.empty()) {
          _result = _tcI0::m_id();
        } else {
          const typename _tcI0::m_carrier &x = l.front();
          std::deque<typename _tcI0::m_carrier> rest =
              std::deque<typename _tcI0::m_carrier>(l.begin() + 1, l.end());
          const auto &m_op0 = _tcI0::m_op;
          _stack.emplace_back(_after_mfold_in_cons{x});
          _stack.emplace_back(_call{std::move(rest)});
        }
      } else {
        auto _f = std::move(std::get<_after_mfold_in_cons>(_popped));
        _stack.pop_back();
        typename _tcI0::m_carrier x = std::move(_f.x);
        const auto &m_op0 = _tcI0::m_op;
        _result = m_op0(std::move(x), std::move(_result));
      }
    }
    return _result;
  }

  static inline const uint64_t test_fold_add =
      crane::any_cast<uint64_t>(mfold<nat_monoid>([](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(1), [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(2), [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(3), std::deque<uint64_t>{})))));
};
