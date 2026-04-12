#ifndef INCLUDED_UNIVERSE_POLY
#define INCLUDED_UNIVERSE_POLY

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct UniversePoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  static inline const unsigned int test_id_nat = poly_id<unsigned int>(42u);
  static inline const bool test_id_bool = poly_id<bool>(true);

  template <typename t_A, typename t_B> struct ppair {
    t_A pfst;
    t_B psnd;
  };

  static inline const std::shared_ptr<ppair<unsigned int, bool>> test_pair =
      std::make_shared<ppair<unsigned int, bool>>(
          ppair<unsigned int, bool>{5u, true});
  static inline const unsigned int test_pfst = test_pair->pfst;
  static inline const bool test_psnd = test_pair->psnd;

  template <typename t_A> struct poption {
    // TYPES
    struct Pnone {};

    struct Psome {
      t_A d_a0;
    };

    using variant_t = std::variant<Pnone, Psome>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit poption(Pnone _v) : d_v_(_v) {}

    explicit poption(Psome _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<poption<t_A>> pnone() {
      return std::make_shared<poption<t_A>>(Pnone{});
    }

    static std::shared_ptr<poption<t_A>> psome(t_A a0) {
      return std::make_shared<poption<t_A>>(Psome{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rect(const T2 f, F1 &&f0,
                         const std::shared_ptr<poption<T1>> &p) {
    return std::visit(
        Overloaded{[&](const typename poption<T1>::Pnone &) -> T2 { return f; },
                   [&](const typename poption<T1>::Psome &_args) -> T2 {
                     return f0(_args.d_a0);
                   }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rec(const T2 f, F1 &&f0,
                        const std::shared_ptr<poption<T1>> &p) {
    return std::visit(
        Overloaded{[&](const typename poption<T1>::Pnone &) -> T2 { return f; },
                   [&](const typename poption<T1>::Psome &_args) -> T2 {
                     return f0(_args.d_a0);
                   }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<poption<T2>>
  poption_map(F0 &&f, const std::shared_ptr<poption<T1>> &o) {
    return std::visit(Overloaded{[](const typename poption<T1>::Pnone &)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::pnone();
                                 },
                                 [&](const typename poption<T1>::Psome &_args)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::psome(f(_args.d_a0));
                                 }},
                      o->v());
  }

  template <typename T1, typename T2,
            MapsTo<std::shared_ptr<poption<T2>>, T1> F1>
  static std::shared_ptr<poption<T2>>
  poption_bind(const std::shared_ptr<poption<T1>> &o, F1 &&f) {
    return std::visit(Overloaded{[](const typename poption<T1>::Pnone &)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::pnone();
                                 },
                                 [&](const typename poption<T1>::Psome &_args)
                                     -> std::shared_ptr<poption<T2>> {
                                   return f(_args.d_a0);
                                 }},
                      o->v());
  }

  static inline const std::shared_ptr<poption<unsigned int>> test_map_some =
      poption_map<unsigned int, unsigned int>(
          [](const unsigned int n) { return (n + 1u); },
          poption<unsigned int>::psome(5u));
  static inline const std::shared_ptr<poption<unsigned int>> test_map_none =
      poption_map<unsigned int, unsigned int>(
          [](const unsigned int n) { return (n + 1u); },
          poption<unsigned int>::pnone());
  static inline const std::shared_ptr<poption<unsigned int>> test_bind =
      poption_bind<unsigned int, unsigned int>(
          poption<unsigned int>::psome(3u), [](const unsigned int n) {
            return poption<unsigned int>::psome((n + n));
          });

  template <typename T1>
  __attribute__((pure)) static unsigned int
  poly_length(const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::Nil &) -> unsigned int { return 0u; },
            [](const typename List<T1>::Cons &_args) -> unsigned int {
              return (poly_length<T1>(_args.d_a1) + 1);
            }},
        l->v());
  }

  static inline const unsigned int test_length =
      poly_length<unsigned int>(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
};

#endif // INCLUDED_UNIVERSE_POLY
