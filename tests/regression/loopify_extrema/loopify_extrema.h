#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
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
};

struct LoopifyExtrema {
  static uint64_t maximum(const List<uint64_t> &l);
  static uint64_t minimum(const List<uint64_t> &l);
  static std::pair<uint64_t, uint64_t> minmax(const List<uint64_t> &l);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t max_by(F0 &&f, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of max_by: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_max_by_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_max_by_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = f(a0);
          } else {
            _stack.emplace_back(_after_max_by_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_after_max_by_in_Cons>(_popped));
        _stack.pop_back();
        uint64_t a0 = _f.a0;
        uint64_t rest_max = _result;
        uint64_t fx = f(a0);
        if (rest_max < fx) {
          _result = fx;
        } else {
          _result = rest_max;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t min_by(F0 &&f, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of min_by: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_min_by_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_min_by_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = f(a0);
          } else {
            _stack.emplace_back(_after_min_by_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_after_min_by_in_Cons>(_popped));
        _stack.pop_back();
        uint64_t a0 = _f.a0;
        uint64_t rest_min = _result;
        uint64_t fx = f(a0);
        if (fx < rest_min) {
          _result = fx;
        } else {
          _result = rest_min;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t argmax(F0 &&f, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of argmax: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_argmax_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_argmax_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_after_argmax_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_after_argmax_in_Cons>(_popped));
        _stack.pop_back();
        uint64_t a0 = _f.a0;
        uint64_t rest_best = _result;
        uint64_t fx = f(a0);
        uint64_t f_rest = f(rest_best);
        if (f_rest < fx) {
          _result = a0;
        } else {
          _result = rest_best;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t argmin(F0 &&f, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of argmin: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_argmin_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_argmin_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_after_argmin_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_after_argmin_in_Cons>(_popped));
        _stack.pop_back();
        uint64_t a0 = _f.a0;
        uint64_t rest_best = _result;
        uint64_t fx = f(a0);
        uint64_t f_rest = f(rest_best);
        if (fx < f_rest) {
          _result = a0;
        } else {
          _result = rest_best;
        }
      }
    }
    return _result;
  }

  static uint64_t lex_compare(const List<uint64_t> &l1,
                              const List<uint64_t> &l2);
  static bool all_equal(const List<uint64_t> &l);
  static bool is_sorted(const List<uint64_t> &l);

  template <typename F0>
  static bool adjacent_all(F0 &&p, const List<uint64_t> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return true;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          return true;
        } else {
          const auto &[a00, _] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (p(a0, a00)) {
            _loop_l = crane_raw(a1);
          } else {
            return false;
          }
        }
      }
    }
  }
};
