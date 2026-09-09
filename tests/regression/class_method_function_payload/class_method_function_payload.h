#ifndef INCLUDED_CLASS_METHOD_FUNCTION_PAYLOAD
#define INCLUDED_CLASS_METHOD_FUNCTION_PAYLOAD

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, A &>
  List<T1> flat_map(F0 &&f) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified flat_map: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.a0).app(std::move(_result));
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// twiceM instantiates bind's second type argument at a *function* type,
/// M (nat -> nat).  The instance bodies do not recover that: MOpt's bind
/// types its payload as uint64_t, so the returned std::function does not
/// convert, and the caller then tries to call a uint64_t.

template <typename I>
concept Monad = requires {
  typename I::template M<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template M<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template M<std::any>>(),
        std::declval<
            std::function<typename I::template M<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template M<std::any>>;
};

struct ClassMethodFunctionPayload {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template M<T3>, F1 &, T2 &>
  static typename _tcI0::template M<T3> bind(typename _tcI0::template M<T2> x,
                                             F1 &&x0) {
    return _tcI0::template bind<T2, T3>(x, x0);
  }

  struct MOpt {
    template <typename _A0> using M = std::optional<_A0>;

    template <typename _A0> static std::optional<_A0> ret(_A0 x) {
      return std::make_optional<_A0>(x);
    }

    template <typename _A0, typename _A1>
    static std::optional<_A1> bind(std::optional<_A0> m,
                                   std::function<std::optional<_A1>(_A0)> f) {
      if (m.has_value()) {
        const _A0 &x = *m;
        return f(x);
      } else {
        return std::optional<_A1>();
      }
    }
  };

  static_assert(Monad<MOpt>);

  struct MList {
    template <typename _A0> using M = List<_A0>;

    template <typename _A0> static List<_A0> ret(_A0 x) {
      return List<_A0>::cons(x, List<std::any>::nil());
    }

    template <typename _A0, typename _A1>
    static List<_A1> bind(List<_A0> m, std::function<List<_A1>(_A0)> f) {
      return m.template flat_map<_A1>(f);
    }
  };

  static_assert(Monad<MList>);

  template <Monad _tcI0>
  static typename _tcI0::template M<std::function<uint64_t(uint64_t)>>
  adders(typename _tcI0::template M<uint64_t> x) {
    return bind<_tcI0, uint64_t, std::function<uint64_t(uint64_t)>>(
        x, [](uint64_t n) {
          return ret<_tcI0, std::function<uint64_t(uint64_t)>>(
              [=](uint64_t k) mutable { return (k + n); });
        });
  }

  static inline const uint64_t run =
      ([]() -> uint64_t {
        auto _cs = adders<MOpt>(std::make_optional<uint64_t>(UINT64_C(3)));
        if (_cs.has_value()) {
          const std::function<uint64_t(uint64_t)> &f = *_cs;
          return f(UINT64_C(1));
        } else {
          return UINT64_C(0);
        }
      }() + adders<MList>(List<uint64_t>::cons(UINT64_C(1),
                                               List<uint64_t>::cons(
                                                   UINT64_C(2),
                                                   List<uint64_t>::nil())))
                       .template fold_left<uint64_t>(
                           [](uint64_t a, std::function<uint64_t(uint64_t)> f) {
                             return (a + f(UINT64_C(1)));
                           },
                           UINT64_C(0)));
};

#endif // INCLUDED_CLASS_METHOD_FUNCTION_PAYLOAD
