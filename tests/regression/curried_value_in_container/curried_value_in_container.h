#ifndef INCLUDED_CURRIED_VALUE_IN_CONTAINER
#define INCLUDED_CURRIED_VALUE_IN_CONTAINER

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
};

struct CurriedValueInContainer {
  /// A curried or partially applied function value stored in a container is
  /// emitted as an uncurried multi-argument lambda.
  template <typename T1, typename T2> static T1 constK(T1 a, const T2 &) {
    return a;
  }

  static inline const uint64_t use =
      ((constK<uint64_t, bool>(UINT64_C(5), true) +
        constK<uint64_t, List<uint64_t>>(
            UINT64_C(6),
            List<uint64_t>::cons(
                UINT64_C(1),
                List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))) +
       constK<uint64_t, std::function<uint64_t(uint64_t)>>(
           UINT64_C(7), [](const auto &n) { return n; }));
  /// Stored in a list and reapplied.
  static inline const List<std::function<uint64_t(uint64_t, uint64_t)>> stored =
      List<std::function<uint64_t(uint64_t, uint64_t)>>::cons(
          constK<uint64_t, uint64_t>,
          List<std::function<uint64_t(uint64_t, uint64_t)>>::cons(
              [](uint64_t a, uint64_t) { return (a * UINT64_C(2)); },
              List<std::function<uint64_t(uint64_t, uint64_t)>>::nil()));
  static inline const uint64_t total =
      (use +
       stored.template fold_left<uint64_t>(
           [](uint64_t acc, std::function<uint64_t(uint64_t, uint64_t)> f) {
             return (acc + f(UINT64_C(3), UINT64_C(4)));
           },
           UINT64_C(0)));
};

#endif // INCLUDED_CURRIED_VALUE_IN_CONTAINER
