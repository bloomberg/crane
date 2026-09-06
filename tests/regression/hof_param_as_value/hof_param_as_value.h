#ifndef INCLUDED_HOF_PARAM_AS_VALUE
#define INCLUDED_HOF_PARAM_AS_VALUE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a1], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<A> a1;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f(std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }
};

struct HofParamAsValue {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t ap(F0 &&f, uint64_t _x0) {
    return f(_x0);
  }

  static inline const List<std::function<uint64_t(uint64_t)>> fs =
      List<std::function<uint64_t(uint64_t)>>::cons(
          [](uint64_t x) { return (x + 1); },
          List<std::function<uint64_t(uint64_t)>>::cons(
              [](uint64_t x) { return (x * UINT64_C(2)); },
              List<std::function<uint64_t(uint64_t)>>::nil()));
  static inline const uint64_t run = fs.template fold_right<uint64_t>(
      [](std::function<uint64_t(uint64_t)> _ec0, uint64_t _ec1) {
        return ap(_ec0, _ec1);
      },
      UINT64_C(1));
};

#endif // INCLUDED_HOF_PARAM_AS_VALUE
