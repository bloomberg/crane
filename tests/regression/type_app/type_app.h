#ifndef INCLUDED_TYPE_APP
#define INCLUDED_TYPE_APP

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<list<t_A>> nil_uptr() {
      return std::make_unique<list<t_A>>(Nil{});
    }

    static std::unique_ptr<list<t_A>>
    cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_unique<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::unique_ptr<list<t_A>>
    cons_uptr(t_A a0, std::shared_ptr<list<t_A>> &&a1) {
      return std::make_unique<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               list_rect<T1, T2>(f, f0, _args.d_a1));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               list_rec<T1, T2>(f, f0, _args.d_a1));
                   }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<list<T2>> map(F0 &&f,
                                       const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename list<T1>::Nil _args)
                       -> std::shared_ptr<list<T2>> { return list<T2>::nil(); },
                   [&](const typename list<T1>::Cons _args)
                       -> std::shared_ptr<list<T2>> {
                     return list<T2>::cons(f(_args.d_a0),
                                           map<T1, T2>(f, _args.d_a1));
                   }},
        l->v());
  }

  static inline const std::shared_ptr<list<unsigned int>> test_map =
      map<unsigned int, unsigned int>(
          [](unsigned int x) { return (x + 1u); },
          list<unsigned int>::cons(
              1u, list<unsigned int>::cons(
                      2u, list<unsigned int>::cons(
                              3u, list<unsigned int>::nil()))));
  static std::shared_ptr<list<unsigned int>>
  map_succ(const std::shared_ptr<list<unsigned int>> &_x0);
  static inline const std::shared_ptr<list<unsigned int>> test_map_succ =
      map_succ(list<unsigned int>::cons(
          5u, list<unsigned int>::cons(6u, list<unsigned int>::nil())));

  template <typename T1, MapsTo<T1, T1> F0>
  static T1 twice(F0 &&f, const T1 x) {
    return f(f(x));
  }

  static inline const unsigned int test_twice =
      twice<unsigned int>([](unsigned int x) { return (x + 1u); }, 10u);

  struct NatMonoid {
    using T = unsigned int;
    static inline const unsigned int empty = 0u;
    __attribute__((pure)) static unsigned int append(const unsigned int _x0,
                                                     const unsigned int _x1);
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
