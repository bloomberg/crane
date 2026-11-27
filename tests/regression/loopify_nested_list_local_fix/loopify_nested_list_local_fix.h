#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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
};

struct LoopifyNestedListLocalFix {
  struct mterm {
    // TYPES
    struct MLit {
      uint64_t a0;
    };

    struct MAdd {
      std::shared_ptr<mterm> a0;
      std::shared_ptr<List<mterm>> a1;
    };

    using variant_t = std::variant<MLit, MAdd>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mterm() {}

    explicit mterm(MLit _v) : v_(std::move(_v)) {}

    explicit mterm(MAdd _v) : v_(std::move(_v)) {}

    static mterm mlit(uint64_t a0) { return mterm(MLit{a0}); }

    static mterm madd(crane::shared_child_slot<mterm> a0, List<mterm> a1) {
      return mterm(
          MAdd{a0.take(), std::make_shared<List<mterm>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mterm() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<MLit>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<mterm>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MAdd>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a1.get();
            while (std::holds_alternative<typename List<mterm>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<mterm>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<mterm>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    mterm(const mterm &) = default;
    mterm &operator=(const mterm &) = default;
    mterm(mterm &&) = default;
    mterm &operator=(mterm &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 mterm_rect(F0 &&f, F1 &&f0, const mterm &m) {
    // Explicit stack replaces the non-tail recursion of mterm_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const mterm *m;
    };

    struct _after_mterm_rect_in_MAdd {
      std::shared_ptr<mterm> a0;
      std::shared_ptr<List<mterm>> a1;
    };

    using _frame = std::variant<_call, _after_mterm_rect_in_MAdd>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const mterm &m = *_f.m;
        if (std::holds_alternative<typename mterm::MLit>(m.v())) {
          const auto &[a0] = std::get<typename mterm::MLit>(m.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename mterm::MAdd>(m.v());
          _stack.emplace_back(_after_mterm_rect_in_MAdd{a0, a1});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_mterm_rect_in_MAdd>(_popped));
        _stack.pop_back();
        std::shared_ptr<mterm> a0 = std::move(_f.a0);
        std::shared_ptr<List<mterm>> a1 = std::move(_f.a1);
        _result = f0(*a0, std::move(_result), *a1);
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
  static T1 mterm_rec(F0 &&f, F1 &&f0, const mterm &m) {
    return mterm_rect<T1>(f, f0, m);
  }

  static mterm h(uint64_t n);
  static mterm h2(uint64_t n);
  static uint64_t size(const mterm &t);
  static inline const uint64_t result =
      size(h(UINT64_C(3))) * UINT64_C(100) + size(h2(UINT64_C(3)));
};
