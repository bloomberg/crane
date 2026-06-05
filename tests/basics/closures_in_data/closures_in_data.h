#ifndef INCLUDED_CLOSURES_IN_DATA
#define INCLUDED_CLOSURES_IN_DATA

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
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

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
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
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }
};

struct ClosuresInData {
  /// A list of functions: successor, doubling, and squaring.
  static inline const List<std::function<uint64_t(uint64_t)>> fn_list =
      List<std::function<uint64_t(uint64_t)>>::cons(
          [](uint64_t x) { return (x + 1); },
          List<std::function<uint64_t(uint64_t)>>::cons(
              [](uint64_t x) { return (x + x); },
              List<std::function<uint64_t(uint64_t)>>::cons(
                  [](uint64_t x) { return (x * x); },
                  List<std::function<uint64_t(uint64_t)>>::nil())));
  /// apply_all fns x applies every function in fns to x,
  /// returning the list of results.
  static List<uint64_t>
  apply_all(const List<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);

  /// A pair of invertible transformations: forward and backward.
  struct transform {
    std::function<uint64_t(uint64_t)> forward;
    std::function<uint64_t(uint64_t)> backward;
  };

  /// A transform that doubles via addition and halves via division.
  static inline const transform double_transform =
      transform{[](uint64_t x) { return (x + x); },
                [](uint64_t x) { return (UINT64_C(2) ? x / UINT64_C(2) : 0); }};
  static uint64_t apply_forward(const transform &t, uint64_t x);
  static uint64_t apply_backward(const transform &t, uint64_t x);
  /// compose_all fns x folds fns left, threading x through each
  /// function in sequence.
  static uint64_t
  compose_all(const List<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);
  /// A pipeline of transformations: increment, double, then add 10.
  static inline const List<std::function<uint64_t(uint64_t)>> pipeline =
      List<std::function<uint64_t(uint64_t)>>::cons(
          [](uint64_t x) { return (x + UINT64_C(1)); },
          List<std::function<uint64_t(uint64_t)>>::cons(
              [](uint64_t x) { return (x * UINT64_C(2)); },
              List<std::function<uint64_t(uint64_t)>>::cons(
                  [](uint64_t x) { return (x + UINT64_C(10)); },
                  List<std::function<uint64_t(uint64_t)>>::nil())));
  /// maybe_apply mf x applies function mf to x if present,
  /// otherwise returns x unchanged.
  static uint64_t
  maybe_apply(const std::optional<std::function<uint64_t(uint64_t)>> &mf,
              uint64_t x);
  static inline const List<uint64_t> test_apply_all =
      apply_all(fn_list, UINT64_C(5));
  static inline const uint64_t test_forward =
      apply_forward(double_transform, UINT64_C(7));
  static inline const uint64_t test_backward =
      apply_backward(double_transform, UINT64_C(14));
  static inline const uint64_t test_compose =
      compose_all(pipeline, UINT64_C(3));
  static inline const uint64_t test_maybe_some =
      maybe_apply(std::make_optional<std::function<uint64_t(uint64_t)>>(
                      [](uint64_t x) { return (x + 1); }),
                  UINT64_C(41));
  static inline const uint64_t test_maybe_none = maybe_apply(
      std::optional<std::function<uint64_t(uint64_t)>>(), UINT64_C(42));
};

#endif // INCLUDED_CLOSURES_IN_DATA
