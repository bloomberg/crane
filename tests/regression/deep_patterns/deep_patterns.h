#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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
  unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<A>::cons _args) -> unsigned int {
                     std::shared_ptr<List<A>> l_ = _args._a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }
};

struct DeepPatterns {
  static unsigned int deep_option(
      const std::optional<std::optional<std::optional<unsigned int>>> x);

  static unsigned int
  deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                            std::pair<unsigned int, unsigned int>>
                p);

  static unsigned int list_shape(const std::shared_ptr<List<unsigned int>> &l);

  struct outer;
  struct inner;
  struct outer {
  public:
    struct OLeft {
      std::shared_ptr<inner> _a0;
    };
    struct ORight {
      unsigned int _a0;
    };
    using variant_t = std::variant<OLeft, ORight>;

  private:
    variant_t v_;
    explicit outer(OLeft _v) : v_(std::move(_v)) {}
    explicit outer(ORight _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<outer> OLeft_(const std::shared_ptr<inner> &a0) {
        return std::shared_ptr<outer>(new outer(OLeft{a0}));
      }
      static std::shared_ptr<outer> ORight_(unsigned int a0) {
        return std::shared_ptr<outer>(new outer(ORight{a0}));
      }
      static std::unique_ptr<outer>
      OLeft_uptr(const std::shared_ptr<inner> &a0) {
        return std::unique_ptr<outer>(new outer(OLeft{a0}));
      }
      static std::unique_ptr<outer> ORight_uptr(unsigned int a0) {
        return std::unique_ptr<outer>(new outer(ORight{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
  struct inner {
  public:
    struct ILeft {
      unsigned int _a0;
    };
    struct IRight {
      bool _a0;
    };
    using variant_t = std::variant<ILeft, IRight>;

  private:
    variant_t v_;
    explicit inner(ILeft _v) : v_(std::move(_v)) {}
    explicit inner(IRight _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<inner> ILeft_(unsigned int a0) {
        return std::shared_ptr<inner>(new inner(ILeft{a0}));
      }
      static std::shared_ptr<inner> IRight_(bool a0) {
        return std::shared_ptr<inner>(new inner(IRight{a0}));
      }
      static std::unique_ptr<inner> ILeft_uptr(unsigned int a0) {
        return std::unique_ptr<inner>(new inner(ILeft{a0}));
      }
      static std::unique_ptr<inner> IRight_uptr(bool a0) {
        return std::unique_ptr<inner>(new inner(IRight{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 outer_rect(F0 &&f, F1 &&f0, const std::shared_ptr<outer> &o) {
    return std::visit(Overloaded{[&](const typename outer::OLeft _args) -> T1 {
                                   std::shared_ptr<inner> i = _args._a0;
                                   return f(std::move(i));
                                 },
                                 [&](const typename outer::ORight _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f0(std::move(n));
                                 }},
                      o->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 outer_rec(F0 &&f, F1 &&f0, const std::shared_ptr<outer> &o) {
    return std::visit(Overloaded{[&](const typename outer::OLeft _args) -> T1 {
                                   std::shared_ptr<inner> i = _args._a0;
                                   return f(std::move(i));
                                 },
                                 [&](const typename outer::ORight _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f0(std::move(n));
                                 }},
                      o->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rect(F0 &&f, F1 &&f0, const std::shared_ptr<inner> &i) {
    return std::visit(Overloaded{[&](const typename inner::ILeft _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename inner::IRight _args) -> T1 {
                                   bool b = _args._a0;
                                   return f0(std::move(b));
                                 }},
                      i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rec(F0 &&f, F1 &&f0, const std::shared_ptr<inner> &i) {
    return std::visit(Overloaded{[&](const typename inner::ILeft _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename inner::IRight _args) -> T1 {
                                   bool b = _args._a0;
                                   return f0(std::move(b));
                                 }},
                      i->v());
  }

  static unsigned int deep_sum(const std::shared_ptr<outer> &o);

  static unsigned int
  complex_match(const std::optional<
                std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>
                    x);

  static unsigned int
  guarded_match(const std::pair<unsigned int, unsigned int> p);

  template <typename A, typename B> struct pair {
  public:
    struct Pair0 {
      A _a0;
      B _a1;
    };
    using variant_t = std::variant<Pair0>;

  private:
    variant_t v_;
    explicit pair(Pair0 _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<pair<A, B>> Pair0_(A a0, B a1) {
        return std::shared_ptr<pair<A, B>>(new pair<A, B>(Pair0{a0, a1}));
      }
      static std::unique_ptr<pair<A, B>> Pair0_uptr(A a0, B a1) {
        return std::unique_ptr<pair<A, B>>(new pair<A, B>(Pair0{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename A> struct mylist {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<mylist<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit mylist(nil _v) : v_(std::move(_v)) {}
    explicit mylist(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<mylist<A>> nil_() {
        return std::shared_ptr<mylist<A>>(new mylist<A>(nil{}));
      }
      static std::shared_ptr<mylist<A>>
      cons_(A a0, const std::shared_ptr<mylist<A>> &a1) {
        return std::shared_ptr<mylist<A>>(new mylist<A>(cons{a0, a1}));
      }
      static std::unique_ptr<mylist<A>> nil_uptr() {
        return std::unique_ptr<mylist<A>>(new mylist<A>(nil{}));
      }
      static std::unique_ptr<mylist<A>>
      cons_uptr(A a0, const std::shared_ptr<mylist<A>> &a1) {
        return std::unique_ptr<mylist<A>>(new mylist<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename mylist<T1>::nil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::cons _args) -> T2 {
              T1 y = _args._a0;
              std::shared_ptr<mylist<T1>> m0 = _args._a1;
              return f0(y, m0, mylist_rect<T1, T2>(f, f0, m0));
            }},
        m->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename mylist<T1>::nil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::cons _args) -> T2 {
              T1 y = _args._a0;
              std::shared_ptr<mylist<T1>> m0 = _args._a1;
              return f0(y, m0, mylist_rec<T1, T2>(f, f0, m0));
            }},
        m->v());
  }

  static unsigned int match_pair_list(
      const std::shared_ptr<
          mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>> &l);

  static unsigned int match_two(const std::shared_ptr<mylist<unsigned int>> &l);

  static unsigned int match_triple(
      const std::shared_ptr<mylist<
          std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>>>> &l);

  static unsigned int
  deep_wildcard(const std::shared_ptr<
                pair<std::shared_ptr<pair<unsigned int, unsigned int>>,
                     std::shared_ptr<pair<unsigned int, unsigned int>>>> &p);

  static inline const unsigned int test_deep_some = deep_option(
      std::make_optional<std::optional<std::optional<unsigned int>>>(
          std::make_optional<std::optional<unsigned int>>(
              std::make_optional<unsigned int>(42u))));

  static inline const unsigned int test_deep_none = deep_option(
      std::make_optional<std::optional<std::optional<unsigned int>>>(
          std::make_optional<std::optional<unsigned int>>(std::nullopt)));

  static inline const unsigned int test_deep_pair =
      deep_pair(std::make_pair(std::make_pair(1u, 2u), std::make_pair(3u, 4u)));

  static inline const unsigned int test_shape_3 =
      list_shape(List<unsigned int>::ctor::cons_(
          10u, List<unsigned int>::ctor::cons_(
                   20u, List<unsigned int>::ctor::cons_(
                            30u, List<unsigned int>::ctor::nil_()))));

  static inline const unsigned int test_shape_long =
      list_shape(List<unsigned int>::ctor::cons_(
          1u,
          List<unsigned int>::ctor::cons_(
              2u,
              List<unsigned int>::ctor::cons_(
                  3u,
                  List<unsigned int>::ctor::cons_(
                      4u,
                      List<unsigned int>::ctor::cons_(
                          5u, List<unsigned int>::ctor::cons_(
                                  6u, List<unsigned int>::ctor::nil_())))))));

  static inline const unsigned int test_deep_sum =
      deep_sum(outer::ctor::OLeft_(inner::ctor::ILeft_(77u)));

  static inline const unsigned int test_complex = complex_match(
      std::make_optional<
          std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>(
          std::make_pair(
              5u,
              List<unsigned int>::ctor::cons_(
                  10u, List<unsigned int>::ctor::cons_(
                           20u, List<unsigned int>::ctor::cons_(
                                    30u, List<unsigned int>::ctor::nil_()))))));

  static inline const unsigned int test_guarded =
      guarded_match(std::make_pair(3u, 7u));

  static inline const unsigned int test_pair_list = match_pair_list(
      mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::cons_(
          pair<unsigned int, unsigned int>::ctor::Pair0_(5u, 3u),
          mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::
              nil_()));

  static inline const unsigned int test_two_one =
      match_two(mylist<unsigned int>::ctor::cons_(
          7u, mylist<unsigned int>::ctor::nil_()));

  static inline const unsigned int test_two_many =
      match_two(mylist<unsigned int>::ctor::cons_(
          7u, mylist<unsigned int>::ctor::cons_(
                  8u, mylist<unsigned int>::ctor::nil_())));

  static inline const unsigned int test_triple = match_triple(
      mylist<std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>>>::
          ctor::cons_(
              mylist<std::shared_ptr<mylist<unsigned int>>>::ctor::cons_(
                  mylist<unsigned int>::ctor::cons_(
                      9u, mylist<unsigned int>::ctor::nil_()),
                  mylist<std::shared_ptr<mylist<unsigned int>>>::ctor::nil_()),
              mylist<std::shared_ptr<mylist<
                  std::shared_ptr<mylist<unsigned int>>>>>::ctor::nil_()));

  static inline const unsigned int test_wildcard = deep_wildcard(
      pair<std::shared_ptr<pair<unsigned int, unsigned int>>,
           std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::
          Pair0_(pair<unsigned int, unsigned int>::ctor::Pair0_(1u, 2u),
                 pair<unsigned int, unsigned int>::ctor::Pair0_(3u, 4u)));

  static inline const unsigned int t =
      ((((((((((((test_deep_some + test_deep_none) + test_deep_pair) +
                test_shape_3) +
               test_shape_long) +
              test_deep_sum) +
             test_complex) +
            test_guarded) +
           test_pair_list) +
          test_two_one) +
         test_two_many) +
        test_triple) +
       test_wildcard);
};
