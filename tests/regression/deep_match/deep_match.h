#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct DeepMatch {
  template <typename A, typename B> struct pair {
  public:
    struct Pair {
      A _a0;
      B _a1;
    };
    using variant_t = std::variant<Pair>;

  private:
    variant_t v_;
    explicit pair(Pair _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<pair<A, B>> Pair_(A a0, B a1) {
        return std::shared_ptr<pair<A, B>>(new pair<A, B>(Pair{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  static unsigned int
  match_pair_list(const std::shared_ptr<
                  list<std::shared_ptr<pair<unsigned int, unsigned int>>>> &l);

  static unsigned int match_two(const std::shared_ptr<list<unsigned int>> &l);

  static unsigned int match_triple(
      const std::shared_ptr<
          list<std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>>> &l);

  static unsigned int
  deep_wildcard(const std::shared_ptr<
                pair<std::shared_ptr<pair<unsigned int, unsigned int>>,
                     std::shared_ptr<pair<unsigned int, unsigned int>>>> &p);

  static inline const unsigned int test_pair_list = match_pair_list(
      list<std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::cons_(
          pair<unsigned int, unsigned int>::ctor::Pair_(5u, 3u),
          list<std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::
              nil_()));

  static inline const unsigned int test_two_one = match_two(
      list<unsigned int>::ctor::cons_(7u, list<unsigned int>::ctor::nil_()));

  static inline const unsigned int test_two_many =
      match_two(list<unsigned int>::ctor::cons_(
          7u, list<unsigned int>::ctor::cons_(
                  8u, list<unsigned int>::ctor::nil_())));

  static inline const unsigned int test_triple = match_triple(
      list<std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>>::ctor::
          cons_(
              list<std::shared_ptr<list<unsigned int>>>::ctor::cons_(
                  list<unsigned int>::ctor::cons_(
                      9u, list<unsigned int>::ctor::nil_()),
                  list<std::shared_ptr<list<unsigned int>>>::ctor::nil_()),
              list<std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>>::
                  ctor::nil_()));

  static inline const unsigned int test_wildcard = deep_wildcard(
      pair<std::shared_ptr<pair<unsigned int, unsigned int>>,
           std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::
          Pair_(pair<unsigned int, unsigned int>::ctor::Pair_(1u, 2u),
                pair<unsigned int, unsigned int>::ctor::Pair_(3u, 4u)));
};
