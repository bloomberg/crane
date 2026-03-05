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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct UniversePoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  static inline const unsigned int test_id_nat = poly_id<unsigned int>((
      (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1));

  static inline const bool test_id_bool = poly_id<bool>(true);

  template <typename A, typename B> struct ppair {
    A pfst;
    B psnd;
  };

  static inline const std::shared_ptr<ppair<unsigned int, bool>> test_pair =
      std::make_shared<ppair<unsigned int, bool>>(
          ppair<unsigned int, bool>{(((((0 + 1) + 1) + 1) + 1) + 1), true});

  static inline const unsigned int test_pfst = test_pair->pfst;

  static inline const bool test_psnd = test_pair->psnd;

  template <typename A> struct poption {
  public:
    struct pnone {};
    struct psome {
      A _a0;
    };
    using variant_t = std::variant<pnone, psome>;

  private:
    variant_t v_;
    explicit poption(pnone _v) : v_(std::move(_v)) {}
    explicit poption(psome _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<poption<A>> pnone_() {
        return std::shared_ptr<poption<A>>(new poption<A>(pnone{}));
      }
      static std::shared_ptr<poption<A>> psome_(A a0) {
        return std::shared_ptr<poption<A>>(new poption<A>(psome{a0}));
      }
      static std::unique_ptr<poption<A>> pnone_uptr() {
        return std::unique_ptr<poption<A>>(new poption<A>(pnone{}));
      }
      static std::unique_ptr<poption<A>> psome_uptr(A a0) {
        return std::unique_ptr<poption<A>>(new poption<A>(psome{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rect(const T2 f, F1 &&f0,
                         const std::shared_ptr<poption<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename poption<T1>::pnone _args) -> T2 { return f; },
            [&](const typename poption<T1>::psome _args) -> T2 {
              T1 a = _args._a0;
              return f0(a);
            }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rec(const T2 f, F1 &&f0,
                        const std::shared_ptr<poption<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename poption<T1>::pnone _args) -> T2 { return f; },
            [&](const typename poption<T1>::psome _args) -> T2 {
              T1 a = _args._a0;
              return f0(a);
            }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<poption<T2>>
  poption_map(F0 &&f, const std::shared_ptr<poption<T1>> &o) {
    return std::visit(Overloaded{[](const typename poption<T1>::pnone _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::ctor::pnone_();
                                 },
                                 [&](const typename poption<T1>::psome _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   T1 x = _args._a0;
                                   return poption<T2>::ctor::psome_(f(x));
                                 }},
                      o->v());
  }

  template <typename T1, typename T2,
            MapsTo<std::shared_ptr<poption<T2>>, T1> F1>
  static std::shared_ptr<poption<T2>>
  poption_bind(const std::shared_ptr<poption<T1>> &o, F1 &&f) {
    return std::visit(Overloaded{[](const typename poption<T1>::pnone _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   return poption<T2>::ctor::pnone_();
                                 },
                                 [&](const typename poption<T1>::psome _args)
                                     -> std::shared_ptr<poption<T2>> {
                                   T1 x = _args._a0;
                                   return f(x);
                                 }},
                      o->v());
  }

  static inline const std::shared_ptr<poption<unsigned int>> test_map_some =
      poption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + (0 + 1)); },
          poption<unsigned int>::ctor::psome_((((((0 + 1) + 1) + 1) + 1) + 1)));

  static inline const std::shared_ptr<poption<unsigned int>> test_map_none =
      poption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + (0 + 1)); },
          poption<unsigned int>::ctor::pnone_());

  static inline const std::shared_ptr<poption<unsigned int>> test_bind =
      poption_bind<unsigned int, unsigned int>(
          poption<unsigned int>::ctor::psome_((((0 + 1) + 1) + 1)),
          [](unsigned int n) {
            return poption<unsigned int>::ctor::psome_((n + n));
          });

  template <typename T1>
  static unsigned int poly_length(const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::nil _args) -> unsigned int {
                     return 0;
                   },
                   [](const typename List<T1>::cons _args) -> unsigned int {
                     std::shared_ptr<List<T1>> rest = _args._a1;
                     return (poly_length<T1>(std::move(rest)) + 1);
                   }},
        l->v());
  }

  static inline const unsigned int test_length =
      poly_length<unsigned int>(List<unsigned int>::ctor::cons_(
          (0 + 1), List<unsigned int>::ctor::cons_(
                       ((0 + 1) + 1), List<unsigned int>::ctor::cons_(
                                          (((0 + 1) + 1) + 1),
                                          List<unsigned int>::ctor::nil_()))));
};
