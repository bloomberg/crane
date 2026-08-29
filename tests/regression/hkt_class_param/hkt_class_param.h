#ifndef INCLUDED_HKT_CLASS_PARAM
#define INCLUDED_HKT_CLASS_PARAM

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
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
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
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
        const List *_self = _f._self;
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
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
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
        const List *_self = _f._self;
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

/// A type class parameterised over a type {i constructor} (C : Type -> Type).
/// Crane emits the instance's methods against the shared List type but
/// erases the element type, producing List<std::any> parameters where
/// List<Nat> is required, which corrupts the mapped List type itself.
template <typename I>
concept Container = requires {
  typename I::template C<std::any>;
  { I::empty() } -> std::convertible_to<typename I::template C<std::any>>;
  {
    I::insert(std::declval<std::any>(),
              std::declval<typename I::template C<std::any>>())
  } -> std::convertible_to<typename I::template C<std::any>>;
  {
    I::toList(std::declval<typename I::template C<std::any>>())
  } -> std::convertible_to<List<std::any>>;
};

struct HktClassParam {
  template <Container _tcI0, typename T2>
  static typename _tcI0::template C<T2> empty() {
    return _tcI0::template empty<T2>();
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::template C<T2>
  insert(const T2 &x, typename _tcI0::template C<T2> x0) {
    return _tcI0::template insert<T2>(x, x0);
  }

  template <Container _tcI0, typename T2>
  static List<T2> toList(typename _tcI0::template C<T2> x) {
    return _tcI0::template toList<T2>(x);
  }

  struct ListContainer {
    template <typename _A0> using C = List<_A0>;

    template <typename _A0 = std::any> static List<_A0> empty() {
      return List<std::any>::nil();
    }

    template <typename _A0 = std::any>
    static List<_A0> insert(_A0 x, List<_A0> xs) {
      return List<std::any>::cons(x, xs);
    }

    template <typename _A0 = std::any> static List<_A0> toList(List<_A0> xs) {
      return xs;
    }
  };

  static_assert(Container<ListContainer>);

  template <Container _tcI0>
  static typename _tcI0::template C<uint64_t> build(const List<uint64_t> &l) {
    return l.template fold_right<typename _tcI0::template C<uint64_t>>(
        [](uint64_t n, typename _tcI0::template C<uint64_t> acc) {
          return insert<_tcI0, uint64_t>(n, acc);
        },
        empty<_tcI0, uint64_t>());
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_HKT_CLASS_PARAM
