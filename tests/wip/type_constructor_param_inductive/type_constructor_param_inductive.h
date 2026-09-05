#ifndef INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE
#define INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
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

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct TypeConstructorParamInductive {
  /// An inductive parameterised by a type {e constructor} emits a template
  /// template parameter that its instantiations do not satisfy.
  template <template <typename> class F, typename A> struct wrapped {
    // TYPES
    struct Wrap {
      F<A> a0;
    };

    struct Pair2 {
      F<A> a0;
      F<A> a1;
    };

    using variant_t = std::variant<Wrap, Pair2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrapped() {}

    explicit wrapped(Wrap _v) : v_(std::move(_v)) {}

    explicit wrapped(Pair2 _v) : v_(std::move(_v)) {}

    template <typename _U0, typename _U1>
    wrapped(const wrapped<_U0, _U1> &_other) {
      if (std::holds_alternative<typename wrapped<_U0, _U1>::Wrap>(
              _other.v())) {
        const auto &[a0] =
            std::get<typename wrapped<_U0, _U1>::Wrap>(_other.v());
        this->v_ = Wrap{F<A>(a0)};
      } else {
        const auto &[a0, a1] =
            std::get<typename wrapped<_U0, _U1>::Pair2>(_other.v());
        this->v_ = Pair2{F<A>(a0), F<A>(a1)};
      }
    }

    static wrapped<F, A> wrap(F<A> a0) {
      return wrapped<F, A>(Wrap{std::move(a0)});
    }

    static wrapped<F, A> pair2(F<A> a0, F<A> a1) {
      return wrapped<F, A>(Pair2{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <template <typename> class T1, typename T2, typename T3, typename F0,
            typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T1<T2> &> &&
             std::is_invocable_r_v<T3, F1 &, T1<T2> &, T1<T2> &>
  static T3 wrapped_rect(F0 &&f, F1 &&f0, const wrapped<T1, T2> &w) {
    if (std::holds_alternative<typename wrapped<T1<std::any>, T2>::Wrap>(
            w.v())) {
      const auto &[a0] =
          std::get<typename wrapped<T1<std::any>, T2>::Wrap>(w.v());
      return f(a0);
    } else {
      const auto &[a0, a1] =
          std::get<typename wrapped<T1<std::any>, T2>::Pair2>(w.v());
      return f0(a0, a1);
    }
  }

  template <template <typename> class T1, typename T2, typename T3, typename F0,
            typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T1<T2> &> &&
             std::is_invocable_r_v<T3, F1 &, T1<T2> &, T1<T2> &>
  static T3 wrapped_rec(F0 &&_x0, F1 &&_x1, const wrapped<T1, T2> &_x2) {
    return [](std::function<T3(T1<T2>)> f, std::function<T3(T1<T2>, T1<T2>)> f0,
              const wrapped<T1, T2> &w) {
      if (std::holds_alternative<typename wrapped<T1<std::any>, T2>::Wrap>(
              w.v())) {
        const auto &[a0] =
            std::get<typename wrapped<T1<std::any>, T2>::Wrap>(w.v());
        return f(a0);
      } else {
        const auto &[a0, a1] =
            std::get<typename wrapped<T1<std::any>, T2>::Pair2>(w.v());
        return f0(a0, a1);
      }
    }(_x0, _x1, _x2);
  }

  static uint64_t size_list(const wrapped<List, uint64_t> &w);
  static uint64_t size_opt(const wrapped<std::optional, uint64_t> &w);
  static inline const uint64_t total =
      (((size_list(wrapped<List, uint64_t>::wrap(List<uint64_t>::cons(
             UINT64_C(1),
             List<uint64_t>::cons(
                 UINT64_C(2),
                 List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))) +
         size_list(wrapped<List, uint64_t>::pair2(
             List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()),
             List<uint64_t>::cons(
                 UINT64_C(2),
                 List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))) +
        size_opt(wrapped<std::optional, uint64_t>::wrap(
            std::make_optional<uint64_t>(UINT64_C(1))))) +
       size_opt(wrapped<std::optional, uint64_t>::pair2(
           std::make_optional<uint64_t>(UINT64_C(1)),
           std::optional<std::any>())));
};

#endif // INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE
