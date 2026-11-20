#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct StackOps {
  struct state_basic {
    List<uint64_t> stack_basic;
  };

  struct state_with_acc {
    List<uint64_t> stack_with_acc;
    uint64_t acc;
  };

  static std::pair<std::optional<uint64_t>, state_basic>
  pop_stack(const state_basic &s);
  static bool is_none(std::optional<uint64_t> o);
  static uint64_t option_or_zero(std::optional<uint64_t> o);
  static inline const bool empty_is_none =
      is_none(pop_stack(state_basic{List<uint64_t>::nil()}).first);
  static inline const uint64_t some_addr =
      option_or_zero(pop_stack(state_basic{List<uint64_t>::cons(
          UINT64_C(9),
          List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil()))})
                         .first);
  static std::pair<std::optional<uint64_t>, state_with_acc>
  pop_stack_acc(const state_with_acc &s);
  static inline const uint64_t pop_acc_test = []() -> uint64_t {
    auto [o, s_] = pop_stack_acc(state_with_acc{List<uint64_t>::cons(
        UINT64_C(9), List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil())),
                                                UINT64_C(3)});
    if (o.has_value()) {
      const uint64_t &a = *o;
      return ((a + s_.stack_with_acc.length()) + s_.acc);
    } else {
      return std::move(s_).acc;
    }
  }();
  static state_basic push_stack(const state_basic &s, uint64_t addr);
  static uint64_t top_or_zero(const state_basic &s);
  static inline const uint64_t empty_len =
      push_stack(state_basic{List<uint64_t>::nil()},
                 UINT64_C(12))
          .stack_basic.length();
  static inline const uint64_t overflow_head =
      top_or_zero(push_stack(state_basic{List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))},
                             UINT64_C(9)));
  static inline const uint64_t overflow_len =
      push_stack(state_basic{List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))},
                 UINT64_C(9))
          .stack_basic.length();
  static state_basic push_stack_cap(const state_basic &s, uint64_t addr);
  static inline const uint64_t push_cap_test =
      push_stack_cap(state_basic{List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(
                  UINT64_C(30),
                  List<uint64_t>::cons(UINT64_C(40), List<uint64_t>::nil()))))},
                     UINT64_C(7))
          .stack_basic.length();
  static inline const std::pair<
      std::pair<std::pair<std::pair<uint64_t, bool>, uint64_t>,
                std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>,
      uint64_t> t = std::make_pair(std::make_pair(
      std::make_pair(std::make_pair(some_addr, empty_is_none), pop_acc_test),
      std::make_pair(std::make_pair(empty_len, overflow_head), overflow_len)),
                                   push_cap_test);
};
