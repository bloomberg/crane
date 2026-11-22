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
};

struct FoldCurriedFixStep {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   uint64_t &>
  static uint64_t g(F0 &&base, const List<uint64_t> &l, uint64_t x0_,
                    uint64_t x1_) {
    return l.template fold_right<
        crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>>(
        [](uint64_t, crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)> acc) {
          auto go =
              [=](List<bool> m, crane::fn<uint64_t(uint64_t, uint64_t)>,
                  uint64_t x0_0, uint64_t x1_0)
                   -> uint64_t {
                // Loop replaces the tail recursion: each recursive call updates
                // the loop variables.
                List<bool> _loop_m = std::move(m);
                while (true) {
                  if (std::holds_alternative<typename List<bool>::Nil>(
                          _loop_m.v_mut())) {
                    return crane::apply2(acc, x0_0, x1_0);
                  } else {
                    auto &[_, a1] =
                        std::get<typename List<bool>::Cons>(_loop_m.v_mut());
                    const List<bool> &a1_value = *a1;
                    _loop_m = List<bool>(a1_value);
                  }
                }
              };
          return [=](uint64_t _pa0,
                     uint64_t _pa1) {
            return go(List<bool>::nil(), acc, _pa0, _pa1);
          };
        },
        [=](uint64_t _ec0) {
          return [=, base = base](uint64_t _ec1) { return base(_ec0, _ec1); };
        })(x0_)(x1_);
  }

  static inline const uint64_t result =
      g([](uint64_t x, uint64_t y) { return ((x * UINT64_C(10)) + y); },
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
        UINT64_C(3), UINT64_C(4));
};
