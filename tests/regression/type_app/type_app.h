#ifndef INCLUDED_TYPE_APP
#define INCLUDED_TYPE_APP

#include <any>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  static inline const uint64_t id_int = id<uint64_t>(UINT64_C(42));
  static inline const bool id_bool = id<bool>(true);

  template <typename T1, typename T2 = void, typename T3, typename F0,
            typename F1>
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

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rec<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
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
  static list<uint64_t> map_succ(const list<uint64_t> &_x0);
  static inline const list<uint64_t> test_map_succ =
      map_succ(list<uint64_t>::cons(
          UINT64_C(5),
          list<uint64_t>::cons(UINT64_C(6), list<uint64_t>::nil())));

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t test_twice = twice<uint64_t>(
      [](uint64_t x) { return (x + UINT64_C(1)); }, UINT64_C(10));

  struct NatMonoid {
    using T = uint64_t;
    static inline const uint64_t empty = UINT64_C(0);
    static uint64_t append(uint64_t _x0, uint64_t _x1);
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
