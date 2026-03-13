#ifndef INCLUDED_DEEP_PATTERNS
#define INCLUDED_DEEP_PATTERNS

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

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }
};

struct DeepPatterns {
  __attribute__((pure)) static unsigned int deep_option(
      const std::optional<std::optional<std::optional<unsigned int>>> x);
  __attribute__((pure)) static unsigned int
  deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                            std::pair<unsigned int, unsigned int>>
                p);
  __attribute__((pure)) static unsigned int
  list_shape(const std::shared_ptr<List<unsigned int>> &l);
  struct outer;
  struct inner;

  struct outer {
    // TYPES
    struct OLeft {
      std::shared_ptr<inner> d_a0;
    };

    struct ORight {
      unsigned int d_a0;
    };

    using variant_t = std::variant<OLeft, ORight>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit outer(OLeft _v) : d_v_(std::move(_v)) {}

    explicit outer(ORight _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
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

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct inner {
    // TYPES
    struct ILeft {
      unsigned int d_a0;
    };

    struct IRight {
      bool d_a0;
    };

    using variant_t = std::variant<ILeft, IRight>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit inner(ILeft _v) : d_v_(std::move(_v)) {}

    explicit inner(IRight _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
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

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 outer_rect(F0 &&f, F1 &&f0, const std::shared_ptr<outer> &o) {
    return std::visit(Overloaded{[&](const typename outer::OLeft _args) -> T1 {
                                   std::shared_ptr<inner> i = _args.d_a0;
                                   return f(std::move(i));
                                 },
                                 [&](const typename outer::ORight _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f0(std::move(n));
                                 }},
                      o->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 outer_rec(F0 &&f, F1 &&f0, const std::shared_ptr<outer> &o) {
    return std::visit(Overloaded{[&](const typename outer::OLeft _args) -> T1 {
                                   std::shared_ptr<inner> i = _args.d_a0;
                                   return f(std::move(i));
                                 },
                                 [&](const typename outer::ORight _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f0(std::move(n));
                                 }},
                      o->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rect(F0 &&f, F1 &&f0, const std::shared_ptr<inner> &i) {
    return std::visit(Overloaded{[&](const typename inner::ILeft _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename inner::IRight _args) -> T1 {
                                   bool b = _args.d_a0;
                                   return f0(std::move(b));
                                 }},
                      i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rec(F0 &&f, F1 &&f0, const std::shared_ptr<inner> &i) {
    return std::visit(Overloaded{[&](const typename inner::ILeft _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename inner::IRight _args) -> T1 {
                                   bool b = _args.d_a0;
                                   return f0(std::move(b));
                                 }},
                      i->v());
  }

  __attribute__((pure)) static unsigned int
  deep_sum(const std::shared_ptr<outer> &o);
  __attribute__((pure)) static unsigned int
  complex_match(const std::optional<
                std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>
                    x);
  __attribute__((pure)) static unsigned int
  guarded_match(const std::pair<unsigned int, unsigned int> p);

  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<pair<t_A, t_B>> Pair0_(t_A a0, t_B a1) {
        return std::shared_ptr<pair<t_A, t_B>>(
            new pair<t_A, t_B>(Pair0{a0, a1}));
      }

      static std::unique_ptr<pair<t_A, t_B>> Pair0_uptr(t_A a0, t_B a1) {
        return std::unique_ptr<pair<t_A, t_B>>(
            new pair<t_A, t_B>(Pair0{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename t_A> struct mylist {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit mylist(Nil _v) : d_v_(std::move(_v)) {}

    explicit mylist(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mylist<t_A>> Nil_() {
        return std::shared_ptr<mylist<t_A>>(new mylist<t_A>(Nil{}));
      }

      static std::shared_ptr<mylist<t_A>>
      Cons_(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
        return std::shared_ptr<mylist<t_A>>(new mylist<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<mylist<t_A>> Nil_uptr() {
        return std::unique_ptr<mylist<t_A>>(new mylist<t_A>(Nil{}));
      }

      static std::unique_ptr<mylist<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
        return std::unique_ptr<mylist<t_A>>(new mylist<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename mylist<T1>::Nil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::Cons _args) -> T2 {
              T1 y = _args.d_a0;
              std::shared_ptr<mylist<T1>> m0 = _args.d_a1;
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
            [&](const typename mylist<T1>::Nil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::Cons _args) -> T2 {
              T1 y = _args.d_a0;
              std::shared_ptr<mylist<T1>> m0 = _args.d_a1;
              return f0(y, m0, mylist_rec<T1, T2>(f, f0, m0));
            }},
        m->v());
  }

  __attribute__((pure)) static unsigned int match_pair_list(
      const std::shared_ptr<
          mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>> &l);
  __attribute__((pure)) static unsigned int
  match_two(const std::shared_ptr<mylist<unsigned int>> &l);
  __attribute__((pure)) static unsigned int match_triple(
      const std::shared_ptr<mylist<
          std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>>>> &l);
  __attribute__((pure)) static unsigned int
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
      list_shape(List<unsigned int>::ctor::Cons_(
          10u, List<unsigned int>::ctor::Cons_(
                   20u, List<unsigned int>::ctor::Cons_(
                            30u, List<unsigned int>::ctor::Nil_()))));
  static inline const unsigned int test_shape_long =
      list_shape(List<unsigned int>::ctor::Cons_(
          1u,
          List<unsigned int>::ctor::Cons_(
              2u,
              List<unsigned int>::ctor::Cons_(
                  3u,
                  List<unsigned int>::ctor::Cons_(
                      4u,
                      List<unsigned int>::ctor::Cons_(
                          5u, List<unsigned int>::ctor::Cons_(
                                  6u, List<unsigned int>::ctor::Nil_())))))));
  static inline const unsigned int test_deep_sum =
      deep_sum(outer::ctor::OLeft_(inner::ctor::ILeft_(77u)));
  static inline const unsigned int test_complex = complex_match(
      std::make_optional<
          std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>(
          std::make_pair(
              5u,
              List<unsigned int>::ctor::Cons_(
                  10u, List<unsigned int>::ctor::Cons_(
                           20u, List<unsigned int>::ctor::Cons_(
                                    30u, List<unsigned int>::ctor::Nil_()))))));
  static inline const unsigned int test_guarded =
      guarded_match(std::make_pair(3u, 7u));
  static inline const unsigned int test_pair_list = match_pair_list(
      mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::Cons_(
          pair<unsigned int, unsigned int>::ctor::Pair0_(5u, 3u),
          mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>::ctor::
              Nil_()));
  static inline const unsigned int test_two_one =
      match_two(mylist<unsigned int>::ctor::Cons_(
          7u, mylist<unsigned int>::ctor::Nil_()));
  static inline const unsigned int test_two_many =
      match_two(mylist<unsigned int>::ctor::Cons_(
          7u, mylist<unsigned int>::ctor::Cons_(
                  8u, mylist<unsigned int>::ctor::Nil_())));
  static inline const unsigned int test_triple = match_triple(
      mylist<std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>>>::
          ctor::Cons_(
              mylist<std::shared_ptr<mylist<unsigned int>>>::ctor::Cons_(
                  mylist<unsigned int>::ctor::Cons_(
                      9u, mylist<unsigned int>::ctor::Nil_()),
                  mylist<std::shared_ptr<mylist<unsigned int>>>::ctor::Nil_()),
              mylist<std::shared_ptr<mylist<
                  std::shared_ptr<mylist<unsigned int>>>>>::ctor::Nil_()));
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

#endif // INCLUDED_DEEP_PATTERNS
