#ifndef INCLUDED_LIFTED_LET_LAMBDA_POLYMORPHIC
#define INCLUDED_LIFTED_LET_LAMBDA_POLYMORPHIC

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

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

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
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

struct LiftedLetLambdaPolymorphic {
  template <typename T1, typename F0>
  static List<crane::fn<T1(T1)>> all(F0 &&op) {
    crane::fn<T1(crane::fn<T1(T1)>, crane::fn<T1(T1)>, T1)> compose =
        [](const crane::fn<T1(T1)> &f, const crane::fn<T1(T1)> &g,
           const T1 &x) { return f(g(x)); };
    return List<crane::fn<T1(T1)>>::cons(
        [=, compose = std::move(compose)](T1 _pa0) {
          return compose(op, op, _pa0);
        },
        List<crane::fn<T1(T1)>>::cons(op, List<crane::fn<T1(T1)>>::nil()));
  }

  static inline const uint64_t from_let =
      all<uint64_t>(
          [](uint64_t _x0) -> uint64_t { return (UINT64_C(2) * _x0); })
          .template fold_left<uint64_t>(
              [](uint64_t a, const crane::fn<uint64_t(uint64_t)> &f) {
                return f(a);
              },
              UINT64_C(1));

  template <typename T1>
  static T1 quad(std::type_identity_t<crane::fn<T1(T1, T1)>> op,
                 const T1 &x0_) {
    crane::fn<T1(T1)> twice = [=, op = std::move(op)](const T1 &x) {
      return op(x, x);
    };
    return twice(twice(x0_));
  }

  static inline const uint64_t from_section = quad<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(1));
};

#endif // INCLUDED_LIFTED_LET_LAMBDA_POLYMORPHIC
