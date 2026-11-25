#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {
  static bool even(uint64_t n);
};

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of fold_right: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_fold_right_in_Cons {
      A a1;
    };

    using _frame = std::variant<_call, _after_fold_right_in_Cons>;
    T1 _result{};
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
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_fold_right_in_Cons{a1});
          _stack.emplace_back(_call{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_after_fold_right_in_Cons>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

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

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename I, typename A>
concept Mon = requires {
  { I::munit() } -> std::convertible_to<A>;
  { I::mop(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<A>;
};

struct LocalFixInlinedDictDestination {
  template <typename T1> struct mon_list {
    static List<T1> munit() { return List<T1>::nil(); }

    static List<T1> mop(List<T1> a0, List<T1> a1) {
      return a0.app(std::move(a1));
    }
  };

  template <typename _tcI0, typename T1>
    requires Mon<_tcI0, T1>
  static T1 mconcat(const List<T1> &l) {
    return l.template fold_right<T1>(_tcI0::mop, _tcI0::munit());
  }

  static inline const uint64_t result = []() {
    return []() {
      auto go_impl = [](auto &_self_go, const List<uint64_t> &l) -> List<bool> {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          return List<bool>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          return List<bool>::cons(Nat::even(a0), _self_go(_self_go, *a1));
        }
      };
      auto go =
          [&](const List<uint64_t> &l) -> List<bool> {
            return go_impl(go_impl, l);
          };
      return go([]() {
        List<uint64_t> l2 =
            List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v_mut())) {
          return List<uint64_t>::nil();
        } else {
          return mconcat<mon_list<uint64_t>, List<uint64_t>>(
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(1),
                      List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
                  List<List<uint64_t>>::cons(
                      List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
                      List<List<uint64_t>>::nil())));
        }
      }().app(List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil())));
    }().length();
  }();
};
