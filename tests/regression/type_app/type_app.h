#ifndef INCLUDED_TYPE_APP
#define INCLUDED_TYPE_APP

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename M>
concept Monoid = requires {
  typename M::T;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::T>;
      });
  {
    M::append(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
};

struct TypeApp {
  template <typename T1> static T1 id(T1 x) { return x; }

  static constexpr uint64_t id_int = UINT64_C(42);
  static constexpr bool id_bool = true;

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T2> &&
             std::is_invocable_r_v<T2, F1 &, const T1 &>
  static T3 compose(F0 &&g, F1 &&f, const T1 &x) {
    return g(f(x));
  }

  template <typename T1> static T1 nested_poly(const T1 &x) {
    return id<T1>(id<T1>(id<T1>(x)));
  }

  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename list<CraneU>::Nil>(
                    _other.v())) {
              return Nil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<list<A>>(crane_convert<list<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list<A>(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rec<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static list<T2> map(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return list<T2>::cons(f(a0), map<T1, T2>(f, *a1));
    }
  }

  static inline const list<uint64_t> test_map = map<uint64_t, uint64_t>(
      [](uint64_t x) { return (x + UINT64_C(1)); },
      list<uint64_t>::cons(
          UINT64_C(1),
          list<uint64_t>::cons(
              UINT64_C(2),
              list<uint64_t>::cons(UINT64_C(3), list<uint64_t>::nil()))));
  static list<uint64_t> map_succ(const list<uint64_t> &x0_);
  static inline const list<uint64_t> test_map_succ =
      map_succ(list<uint64_t>::cons(
          UINT64_C(5),
          list<uint64_t>::cons(UINT64_C(6), list<uint64_t>::nil())));

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static constexpr uint64_t test_twice = UINT64_C(12);

  struct NatMonoid {
    using T = uint64_t;
    static constexpr uint64_t empty = UINT64_C(0);
    static uint64_t append(uint64_t x0_, uint64_t x1_);
  };

  template <Monoid M> struct UseMonoid {
    static const typename M::T &combine_empty() {
      static const typename M::T v = M::append(M::empty, M::empty);
      return v;
    }

    static typename M::T triple(typename M::T x) {
      return M::append(x, M::append(x, x));
    }
  };

  using NatMonoidUser = UseMonoid<NatMonoid>;
  static inline const NatMonoid::T monoid_test = NatMonoidUser::combine_empty();
};

#endif // INCLUDED_TYPE_APP
