#ifndef INCLUDED_DEEP_PATTERNS
#define INCLUDED_DEEP_PATTERNS

#include <memory>
#include <optional>
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

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil &) -> unsigned int { return 0u; },
            [](const typename List<t_A>::Cons &_args) -> unsigned int {
              return (_args.d_a1->length() + 1);
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

  public:
    // CREATORS
    explicit outer(OLeft _v) : d_v_(std::move(_v)) {}

    explicit outer(ORight _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<outer> oleft(const std::shared_ptr<inner> &a0) {
      return std::make_shared<outer>(OLeft{a0});
    }

    static std::shared_ptr<outer> oleft(std::shared_ptr<inner> &&a0) {
      return std::make_shared<outer>(OLeft{std::move(a0)});
    }

    static std::shared_ptr<outer> oright(unsigned int a0) {
      return std::make_shared<outer>(ORight{std::move(a0)});
    }

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

  public:
    // CREATORS
    explicit inner(ILeft _v) : d_v_(std::move(_v)) {}

    explicit inner(IRight _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<inner> ileft(unsigned int a0) {
      return std::make_shared<inner>(ILeft{std::move(a0)});
    }

    static std::shared_ptr<inner> iright(bool a0) {
      return std::make_shared<inner>(IRight{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 outer_rect(F0 &&f, F1 &&f0, const std::shared_ptr<outer> &o) {
    return std::visit(
        Overloaded{[&](const typename outer::OLeft &_args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename outer::ORight &_args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        o->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 outer_rec(F0 &&f, F1 &&f0, const std::shared_ptr<outer> &o) {
    return std::visit(
        Overloaded{[&](const typename outer::OLeft &_args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename outer::ORight &_args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        o->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rect(F0 &&f, F1 &&f0, const std::shared_ptr<inner> &i) {
    return std::visit(
        Overloaded{[&](const typename inner::ILeft &_args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename inner::IRight &_args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rec(F0 &&f, F1 &&f0, const std::shared_ptr<inner> &i) {
    return std::visit(
        Overloaded{[&](const typename inner::ILeft &_args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename inner::IRight &_args) -> T1 {
                     return f0(_args.d_a0);
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

  public:
    // CREATORS
    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pair<t_A, t_B>> pair0(t_A a0, t_B a1) {
      return std::make_shared<pair<t_A, t_B>>(
          Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename pair<t_A, t_B>::Pair0 &_args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename pair<t_A, t_B>::Pair0 &_args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }
  };

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

  public:
    // CREATORS
    explicit mylist(Nil _v) : d_v_(_v) {}

    explicit mylist(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist<t_A>> nil() {
      return std::make_shared<mylist<t_A>>(Nil{});
    }

    static std::shared_ptr<mylist<t_A>>
    cons(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_shared<mylist<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist<t_A>>
    cons(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_shared<mylist<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

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
        Overloaded{[&](const typename mylist<T1>::Nil &) -> T2 { return f; },
                   [&](const typename mylist<T1>::Cons &_args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               mylist_rect<T1, T2>(f, f0, _args.d_a1));
                   }},
        m->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{[&](const typename mylist<T1>::Nil &) -> T2 { return f; },
                   [&](const typename mylist<T1>::Cons &_args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               mylist_rec<T1, T2>(f, f0, _args.d_a1));
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
          std::make_optional<std::optional<unsigned int>>(
              std::optional<unsigned int>())));
  static inline const unsigned int test_deep_pair =
      deep_pair(std::make_pair(std::make_pair(1u, 2u), std::make_pair(3u, 4u)));
  static inline const unsigned int test_shape_3 =
      list_shape(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil()))));
  static inline const unsigned int test_shape_long =
      list_shape(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u,
              List<unsigned int>::cons(
                  3u, List<unsigned int>::cons(
                          4u, List<unsigned int>::cons(
                                  5u, List<unsigned int>::cons(
                                          6u, List<unsigned int>::nil())))))));
  static inline const unsigned int test_deep_sum =
      deep_sum(outer::oleft(inner::ileft(77u)));
  static inline const unsigned int test_complex = complex_match(
      std::make_optional<
          std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>(
          std::make_pair(
              5u, List<unsigned int>::cons(
                      10u, List<unsigned int>::cons(
                               20u, List<unsigned int>::cons(
                                        30u, List<unsigned int>::nil()))))));
  static inline const unsigned int test_guarded =
      guarded_match(std::make_pair(3u, 7u));
  static inline const unsigned int test_pair_list = match_pair_list(
      mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>::cons(
          pair<unsigned int, unsigned int>::pair0(5u, 3u),
          mylist<std::shared_ptr<pair<unsigned int, unsigned int>>>::nil()));
  static inline const unsigned int test_two_one =
      match_two(mylist<unsigned int>::cons(7u, mylist<unsigned int>::nil()));
  static inline const unsigned int test_two_many =
      match_two(mylist<unsigned int>::cons(
          7u, mylist<unsigned int>::cons(8u, mylist<unsigned int>::nil())));
  static inline const unsigned int test_triple = match_triple(
      mylist<std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>>>::
          cons(mylist<std::shared_ptr<mylist<unsigned int>>>::cons(
                   mylist<unsigned int>::cons(9u, mylist<unsigned int>::nil()),
                   mylist<std::shared_ptr<mylist<unsigned int>>>::nil()),
               mylist<std::shared_ptr<
                   mylist<std::shared_ptr<mylist<unsigned int>>>>>::nil()));
  static inline const unsigned int test_wildcard =
      deep_wildcard(pair<std::shared_ptr<pair<unsigned int, unsigned int>>,
                         std::shared_ptr<pair<unsigned int, unsigned int>>>::
                        pair0(pair<unsigned int, unsigned int>::pair0(1u, 2u),
                              pair<unsigned int, unsigned int>::pair0(3u, 4u)));
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
