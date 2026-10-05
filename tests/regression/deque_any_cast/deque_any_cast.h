#ifndef INCLUDED_DEQUE_ANY_CAST
#define INCLUDED_DEQUE_ANY_CAST

#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <deque>
#include <utility>
#include <variant>

template <typename
I>concept Monoid = requires {
    typename I::m_carrier;
    { I::m_op(std::declval<typename I::m_carrier>(), std::declval<typename I::m_carrier>()) } -> std::convertible_to<typename I::m_carrier>;
  } && (requires {
    { I::m_id() } -> std::convertible_to<typename I::m_carrier>;
  } || requires {
    { I::m_id } -> std::convertible_to<typename I::m_carrier>;
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
  mfold(const std::deque<typename _tcI0::m_carrier>
            &l) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

    struct CraneEnter {
      std::deque<typename _tcI0::m_carrier> l;
    };

    /// CraneCont_x: saves [x], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_x {
      typename _tcI0::m_carrier x;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_x>;
    typename _tcI0::m_carrier _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{l});
    /// Loopified mfold: CraneEnter -> CraneCont_x.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const std::deque<typename _tcI0::m_carrier> &l = std::move(_f.l);
        if (l.empty()) {
          _result = _tcI0::m_id();
        } else {
          const auto &x = l.front();
          std::deque<typename _tcI0::m_carrier> rest(l.begin() + 1, l.end());
          const auto &m_op0 = _tcI0::m_op;
          crane::obj _x = _tcI0::m_id;
          _stack.emplace_back(CraneCont_x{x});
          _stack.emplace_back(CraneEnter{rest});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_x>(_frame));
        typename _tcI0::m_carrier x = std::move(_f.x);
        const auto &m_op0 = _tcI0::m_op;
        _result = m_op0(x, std::move(_result));
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

#endif // INCLUDED_DEQUE_ANY_CAST
