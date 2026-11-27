#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
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
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

struct ExistentialCtorErasedFn {
  /// The same erased-function-parameter failure reached through a user
  /// inductive with an existential constructor rather than through sigT.
  struct dynamic {
    // DATA
    crane::obj a;
    crane::fn<uint64_t(crane::obj)> a1;

    // ACCESSORS
    dynamic clone() const { return {a, a1}; }

    // CREATORS
    static dynamic dyn(crane::obj a, crane::fn<uint64_t(crane::obj)> a1) {
      return {std::move(a), std::move(a1)};
    }
  };

  template <typename T1, typename F0>
  static T1 dynamic_rect(F0 &&f, const dynamic &d) {
    const auto &[a0, a1] = d;
    return crane_any_cast<T1>(f(a0, a1));
  }

  template <typename T1, typename F0>
  static T1 dynamic_rec(F0 &&f, const dynamic &d) {
    return dynamic_rect<T1>(f, d);
  }

  static uint64_t read(const dynamic &d);
  static inline const List<dynamic> items = List<dynamic>::cons(
      dynamic::dyn(UINT64_C(7), crane::fn<uint64_t(crane::obj)>(
                                    [](const crane::obj &n) -> uint64_t {
                                      return crane::any_cast<uint64_t>(n);
                                    })),
      List<dynamic>::cons(
          dynamic::dyn(true, crane::fn<uint64_t(crane::obj)>(
                                 [](const crane::obj &b) -> uint64_t {
                                   if (crane::any_cast<bool>(b)) {
                                     return UINT64_C(1);
                                   } else {
                                     return UINT64_C(0);
                                   }
                                 })),
          List<dynamic>::cons(
              dynamic::dyn(
                  List<crane::obj>::cons(
                      UINT64_C(1),
                      List<crane::obj>::cons(
                          UINT64_C(2),
                          List<crane::obj>::cons(UINT64_C(3),
                                                 List<crane::obj>::nil()))),
                  crane_erase_fn<uint64_t>(
                      [](const List<crane::obj> &_x) { return _x.length(); })),
              List<dynamic>::nil())));
  static inline const uint64_t total = items.template fold_left<uint64_t>(
      [](uint64_t acc, const dynamic &d) { return (acc + read(d)); },
      UINT64_C(0));
};
