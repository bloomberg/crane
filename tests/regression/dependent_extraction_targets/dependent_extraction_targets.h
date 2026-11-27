#pragma once

#include "crane_fn.h"
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

struct DependentExtractionTargets {
  struct Inner {
    struct t {
      // TYPES
      struct A {};

      struct B {
        uint64_t a0;
      };

      using variant_t = std::variant<A, B>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t() {}

      explicit t(A _v) : v_(_v) {}

      explicit t(B _v) : v_(std::move(_v)) {}

      static t a() { return t(A{}); }

      static t b(uint64_t a0) { return t(B{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const uint64_t &>
    static T1 t_rect(T1 f0, F1 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::A>(t0.v())) {
        return f0;
      } else {
        const auto &[a0] = std::get<typename t::B>(t0.v());
        return f1(a0);
      }
    }

    template <typename T1, typename F1>
    static T1 t_rec(T1 f0, F1 &&f1, const t &t0) {
      return t_rect<T1>(std::move(f0), f1, t0);
    }

    static uint64_t f(const t &x);

    struct Deep {
      static inline const uint64_t g = f(t::b(UINT64_C(4)));
    };
  };

  struct A {
    struct t {
      // DATA
      uint64_t a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t t0(uint64_t a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    static T1 t_rect(F0 &&f0, const t &t0) {
      const auto &[a0] = t0;
      return f0(a0);
    }

    template <typename T1, typename F0> static T1 t_rec(F0 &&f0, const t &t0) {
      return t_rect<T1>(f0, t0);
    }

    static uint64_t get(const t &x);
  };

  struct B {
    static inline const uint64_t use = A::get(A::t::t0(UINT64_C(9)));
  };

  template <typename T1> static List<T1> rep(const T1 &z, uint64_t n) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t m = n - 1;
      return List<T1>::cons(z, rep<T1>(z, m));
    }
  }

  static inline const uint64_t result =
      ((Inner::Deep::g + B::use) +
       rep<uint64_t>(UINT64_C(7), UINT64_C(3)).length());
};
