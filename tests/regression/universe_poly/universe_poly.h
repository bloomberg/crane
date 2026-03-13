#ifndef INCLUDED_UNIVERSE_POLY
#define INCLUDED_UNIVERSE_POLY

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

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

    // CREATORS
    explicit poption(Pnone _v) : d_v_(std::move(_v)) {}

    explicit poption(Psome _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<poption<t_A>> Pnone_() {
        return std::shared_ptr<poption<t_A>>(new poption<t_A>(Pnone{}));
      }

      static std::shared_ptr<poption<t_A>> Psome_(t_A a0) {
        return std::shared_ptr<poption<t_A>>(new poption<t_A>(Psome{a0}));
      }

      static std::unique_ptr<poption<t_A>> Pnone_uptr() {
        return std::unique_ptr<poption<t_A>>(new poption<t_A>(Pnone{}));
      }

      static std::unique_ptr<poption<t_A>> Psome_uptr(t_A a0) {
        return std::unique_ptr<poption<t_A>>(new poption<t_A>(Psome{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rect(const T2 f, F1 &&f0,
                         const std::shared_ptr<poption<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename poption<T1>::Pnone _args) -> T2 { return f; },
            [&](const typename poption<T1>::Psome _args) -> T2 {
              T1 a = _args.d_a0;
              return f0(a);
            }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rec(const T2 f, F1 &&f0,
                        const std::shared_ptr<poption<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename poption<T1>::Pnone _args) -> T2 { return f; },
            [&](const typename poption<T1>::Psome _args) -> T2 {
              T1 a = _args.d_a0;
              return f0(a);
            }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<poption<T2>>
  poption_map(F0 &&f, const std::shared_ptr<poption<T1>> &o) {
    return std::visit(Overloaded{[](const typename poption<T1>::Pnone _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::ctor::Pnone_();
                                 },
                                 [&](const typename poption<T1>::Psome _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   T1 x = _args.d_a0;
                                   return poption<T2>::ctor::Psome_(f(x));
                                 }},
                      o->v());
  }

  template <typename T1, typename T2,
            MapsTo<std::shared_ptr<poption<T2>>, T1> F1>
  static std::shared_ptr<poption<T2>>
  poption_bind(const std::shared_ptr<poption<T1>> &o, F1 &&f) {
    return std::visit(Overloaded{[](const typename poption<T1>::Pnone _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::ctor::Pnone_();
                                 },
                                 [&](const typename poption<T1>::Psome _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   T1 x = _args.d_a0;
                                   return f(x);
                                 }},
                      o->v());
  }

  static inline const std::shared_ptr<poption<unsigned int>> test_map_some =
      poption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + 1u); },
          poption<unsigned int>::ctor::Psome_(5u));
  static inline const std::shared_ptr<poption<unsigned int>> test_map_none =
      poption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + 1u); },
          poption<unsigned int>::ctor::Pnone_());
  static inline const std::shared_ptr<poption<unsigned int>> test_bind =
      poption_bind<unsigned int, unsigned int>(
          poption<unsigned int>::ctor::Psome_(3u), [](unsigned int n) {
            return poption<unsigned int>::ctor::Psome_((n + n));
          });

  template <typename T1>
  __attribute__((pure)) static unsigned int
  poly_length(const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<T1>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<T1>> rest = _args.d_a1;
                     return (poly_length<T1>(std::move(rest)) + 1);
                   }},
        l->v());
  }

  static inline const unsigned int test_length =
      poly_length<unsigned int>(List<unsigned int>::ctor::Cons_(
          1u, List<unsigned int>::ctor::Cons_(
                  2u, List<unsigned int>::ctor::Cons_(
                          3u, List<unsigned int>::ctor::Nil_()))));
};

#endif // INCLUDED_UNIVERSE_POLY
