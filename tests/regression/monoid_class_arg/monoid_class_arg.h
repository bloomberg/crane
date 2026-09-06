#ifndef INCLUDED_MONOID_CLASS_ARG
#define INCLUDED_MONOID_CLASS_ARG

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
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

template <typename I, typename A>
concept Monoid = requires {
  { I::unit_() } -> std::convertible_to<A>;
  { I::op(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<A>;
};

struct MonoidClassArg {
  struct MNat {
    static uint64_t unit_() { return UINT64_C(0); }

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Monoid<MNat, uint64_t>);

  template <typename T1> struct MList {
    static List<T1> unit_() { return List<T1>::nil(); }

    static List<T1> op(List<T1> a0, List<T1> a1) { return a0.app(a1); }
  };

  template <typename _tcI0, typename _tcI1, typename T1, typename T2>
    requires Monoid<_tcI0, T1> && Monoid<_tcI1, T2>
  struct MPair {
    static std::pair<T1, T2> unit_() {
      return std::make_pair(_tcI0::unit_(), _tcI1::unit_());
    }

    static std::pair<T1, T2> op(std::pair<T1, T2> p, std::pair<T1, T2> q) {
      return std::make_pair(_tcI0::op(p.first, q.first),
                            _tcI1::op(p.second, q.second));
    }
  };

  template <typename _tcI0, typename T1>
    requires Monoid<_tcI0, T1>
  static T1 mconcat(const List<T1> &l) {
    return l.template fold_right<T1>(_tcI0::op, _tcI0::unit_());
  }

  static inline const uint64_t run =
      ((mconcat<MNat, uint64_t>(List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))) +
        mconcat<MList<uint64_t>, List<uint64_t>>(
            List<List<uint64_t>>::cons(
                List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()),
                List<List<uint64_t>>::cons(
                    List<uint64_t>::cons(
                        UINT64_C(2), List<uint64_t>::cons(
                                         UINT64_C(3), List<uint64_t>::nil())),
                    List<List<uint64_t>>::nil())))
            .length()) +
       mconcat<MPair<MNat, MList<uint64_t>, uint64_t, List<uint64_t>>,
               std::pair<uint64_t, List<uint64_t>>>(
           List<std::pair<uint64_t, List<uint64_t>>>::cons(
               std::make_pair(
                   UINT64_C(1),
                   List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil())),
               List<std::pair<uint64_t, List<uint64_t>>>::cons(
                   std::make_pair(UINT64_C(2),
                                  List<uint64_t>::cons(UINT64_C(2),
                                                       List<uint64_t>::nil())),
                   List<std::pair<uint64_t, List<uint64_t>>>::nil())))
           .first);
};

#endif // INCLUDED_MONOID_CLASS_ARG
