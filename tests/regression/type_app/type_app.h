#ifndef INCLUDED_TYPE_APP
#define INCLUDED_TYPE_APP

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const unsigned int id_int = id<unsigned int>(42u);
  static inline const bool id_bool = id<bool>(true);

  template <typename T1, typename T2 = void, typename T3, typename F0,
            typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  template <typename T1> static T1 nested_poly(const T1 x) {
    return id<T1>(id<T1>(id<T1>(x)));
  }

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(Cons{
            d_a0, d_a1 ? std::make_unique<TypeApp::list<t_A>>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(d_a0, *(d_a1), list_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(d_a0, *(d_a1), list_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static list<T2> map(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return list<T2>::cons(f(d_a0), map<T1, T2>(f, *(d_a1)));
    }
  }

  static inline const list<unsigned int> test_map =
      map<unsigned int, unsigned int>(
          [](const unsigned int &x) { return (x + 1u); },
          list<unsigned int>::cons(
              1u, list<unsigned int>::cons(
                      2u, list<unsigned int>::cons(
                              3u, list<unsigned int>::nil()))));
  __attribute__((pure)) static list<unsigned int>
  map_succ(const list<unsigned int> &_x0);
  static inline const list<unsigned int> test_map_succ =
      map_succ(list<unsigned int>::cons(
          5u, list<unsigned int>::cons(6u, list<unsigned int>::nil())));

  template <typename T1, MapsTo<T1, T1> F0>
  static T1 twice(F0 &&f, const T1 x) {
    return f(f(x));
  }

  static inline const unsigned int test_twice =
      twice<unsigned int>([](const unsigned int &x) { return (x + 1u); }, 10u);

  struct NatMonoid {
    using T = unsigned int;
    static inline const unsigned int empty = 0u;
    __attribute__((pure)) static unsigned int append(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  };

  template <Monoid M> struct UseMonoid {
    static const typename M::T &combine_empty() {
      static const typename M::T v = M::append(M::empty, M::empty);
      return v;
    }

    constexpr static typename M::T triple(const typename M::T x) {
      return M::append(x, M::append(x, x));
    }
  };

  using NatMonoidUser = UseMonoid<NatMonoid>;
  static inline const NatMonoid::T monoid_test = NatMonoidUser::combine_empty();
};

#endif // INCLUDED_TYPE_APP
