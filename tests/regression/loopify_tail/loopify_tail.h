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

struct LoopifyTail {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (l ? std::make_shared<list<A>>(crane_convert<list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a, crane::shared_child_slot<list<A>> l) {
      return list<A>(Cons{std::move(a), l.take()});
    }

    // MANIPULATORS
    ~list() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    // Explicit stack replaces the non-tail recursion of list_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const list<T1> *l;
    };

    struct _after_list_rect_in_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
    };

    using _frame = std::variant<_call, _after_list_rect_in_Cons>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_after_list_rect_in_Cons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_list_rect_in_Cons>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    return list_rect<T1, T2>(std::move(f), f0, l);
  }

  /// Tail-recursive: last element of a list
  template <typename T1> static T1 last(T1 x, const list<T1> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const list<T1> *_loop_l = &l;
    T1 _loop_x = std::move(x);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return _loop_x;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a1);
        _loop_x = a0;
      }
    }
  }

  /// Tail-recursive: length with accumulator
  template <typename T1>
  static uint64_t length_acc(uint64_t acc, const list<T1> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const list<T1> *_loop_l = &l;
    uint64_t _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[_, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a1);
        _loop_acc = (_loop_acc + 1);
      }
    }
  }

  template <typename T1> static uint64_t length(const list<T1> &l) {
    return length_acc<T1>(UINT64_C(0), l);
  }

  /// Tail-recursive: membership test
  static bool member(uint64_t x, const list<uint64_t> &l);
  /// Tail-recursive: nth element
  static uint64_t nth(uint64_t n, const list<uint64_t> &l, uint64_t default0);

  /// Tail-recursive: fold_left
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &&, const T1 &>
  static T2 fold_left(F0 &&f, T2 acc, const list<T1> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const list<T1> *_loop_l = &l;
    T2 _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a1);
        _loop_acc = f(std::move(_loop_acc), a0);
      }
    }
  }

  /// Tail-recursive: lookup in association list
  static uint64_t lookup(uint64_t key,
                         const list<std::pair<uint64_t, uint64_t>> &l);
};
