#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Bool0 {
  struct bool0 {
  public:
    struct true0 {};
    struct false0 {};
    using variant_t = std::variant<true0, false0>;

  private:
    variant_t v_;
    explicit bool0(true0 _v) : v_(std::move(_v)) {}
    explicit bool0(false0 _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Bool0::bool0> true0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(true0{}));
      }
      static std::shared_ptr<Bool0::bool0> false0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(false0{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct ImplicitArgs {
  template <typename T1> static T1 id(const T1 x) { return x; }

  template <typename T1, typename T2>
  static T1 fst_of(const T1 x, const T2 _x) {
    return x;
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 apply(F0 &&f, const T1 _x0) {
    return f(_x0);
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T2> F0,
            MapsTo<T2, T1> F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  template <typename A> struct mylist {
  public:
    struct mynil {};
    struct mycons {
      A _a0;
      std::shared_ptr<mylist<A>> _a1;
    };
    using variant_t = std::variant<mynil, mycons>;

  private:
    variant_t v_;
    explicit mylist(mynil _v) : v_(std::move(_v)) {}
    explicit mylist(mycons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<mylist<A>> mynil_() {
        return std::shared_ptr<mylist<A>>(new mylist<A>(mynil{}));
      }
      static std::shared_ptr<mylist<A>>
      mycons_(A a0, const std::shared_ptr<mylist<A>> &a1) {
        return std::shared_ptr<mylist<A>>(new mylist<A>(mycons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename mylist<T1>::mynil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::mycons _args) -> T2 {
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
            [&](const typename mylist<T1>::mynil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::mycons _args) -> T2 {
              T1 y = _args._a0;
              std::shared_ptr<mylist<T1>> m0 = _args._a1;
              return f0(y, m0, mylist_rec<T1, T2>(f, f0, m0));
            }},
        m->v());
  }

  template <typename T1>
  static unsigned int length(const std::shared_ptr<mylist<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename mylist<T1>::mynil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename mylist<T1>::mycons _args) -> unsigned int {
                     std::shared_ptr<mylist<T1>> rest = _args._a1;
                     return (1u + length<T1>(rest));
                   }},
        l->v());
  }

  static inline const unsigned int explicit_id = id<unsigned int>(5u);

  static inline const unsigned int explicit_fst =
      fst_of<unsigned int, std::shared_ptr<Bool0::bool0>>(
          3u, Bool0::bool0::ctor::true0_());

  static unsigned int add_one(const unsigned int);

  static unsigned int double_nat(const unsigned int n);

  static unsigned int add_implicit(const unsigned int, const unsigned int);

  static inline const unsigned int use_add_implicit = add_implicit(5u, 3u);

  static unsigned int scale(const unsigned int, const unsigned int);

  static inline const unsigned int use_scale = scale(3u, 7u);

  static unsigned int combine(const unsigned int a, const unsigned int b,
                              const unsigned int x);

  static inline const unsigned int use_combine = combine(2u, 3u, 4u);

  template <MapsTo<unsigned int, unsigned int> F0>
  static unsigned int apply_implicit(F0 &&f, const unsigned int _x0) {
    return f(_x0);
  }

  static inline const unsigned int use_apply_implicit =
      apply_implicit([](const unsigned int _x0) { return (1u + _x0); }, 5u);

  static unsigned int with_base(const unsigned int, const unsigned int);

  static unsigned int from_zero(const unsigned int);

  static unsigned int from_ten(const unsigned int);

  static inline const unsigned int use_from_zero = from_zero(5u);

  static inline const unsigned int use_from_ten = from_ten(5u);

  template <typename T1>
  static T1 head_or(const T1 default0, const std::shared_ptr<mylist<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename mylist<T1>::mynil _args) -> T1 {
                     return default0;
                   },
                   [](const typename mylist<T1>::mycons _args) -> T1 {
                     T1 x = _args._a0;
                     return x;
                   }},
        l->v());
  }

  static inline const unsigned int use_head_empty =
      head_or<unsigned int>(0u, mylist<unsigned int>::ctor::mynil_());

  static inline const unsigned int use_head_nonempty =
      head_or<unsigned int>(0u, mylist<unsigned int>::ctor::mycons_(
                                    7u, mylist<unsigned int>::ctor::mynil_()));

  static unsigned int
  sum_with_init(const unsigned int init,
                const std::shared_ptr<mylist<unsigned int>> &l);

  static inline const unsigned int use_sum_init =
      sum_with_init(5u, mylist<unsigned int>::ctor::mycons_(
                            1u, mylist<unsigned int>::ctor::mycons_(
                                    2u, mylist<unsigned int>::ctor::mynil_())));

  static unsigned int nested_implicits(const unsigned int a,
                                       const unsigned int b,
                                       const unsigned int c);

  static inline const unsigned int use_nested = nested_implicits(1u, 2u, 3u);

  static unsigned int choose_branch(const std::shared_ptr<Bool0::bool0> &flag,
                                    const unsigned int t, const unsigned int f);

  static inline const unsigned int use_choose_true =
      choose_branch(Bool0::bool0::ctor::true0_(), 7u, 3u);

  static inline const unsigned int use_choose_false =
      choose_branch(Bool0::bool0::ctor::false0_(), 7u, 3u);

  static inline const unsigned int test_id = id<unsigned int>(5u);

  static inline const unsigned int test_fst =
      fst_of<unsigned int, unsigned int>(3u, 7u);

  static inline const unsigned int test_apply =
      apply<unsigned int, unsigned int>(double_nat, 5u);

  static inline const unsigned int test_compose =
      compose<unsigned int, unsigned int, unsigned int>(
          double_nat, [](const unsigned int _x0) { return (1u + _x0); }, 3u);

  static inline const unsigned int test_length =
      length<unsigned int>(mylist<unsigned int>::ctor::mycons_(
          1u, mylist<unsigned int>::ctor::mycons_(
                  2u, mylist<unsigned int>::ctor::mycons_(
                          3u, mylist<unsigned int>::ctor::mynil_()))));

  static inline const unsigned int test_explicit_id = explicit_id;

  static inline const unsigned int test_explicit_fst = explicit_fst;

  static inline const unsigned int test_add_implicit = use_add_implicit;

  static inline const unsigned int test_scale = use_scale;

  static inline const unsigned int test_combine = use_combine;

  static inline const unsigned int test_apply_implicit = use_apply_implicit;

  static inline const unsigned int test_from_zero = use_from_zero;

  static inline const unsigned int test_from_ten = use_from_ten;

  static inline const unsigned int test_head_empty = use_head_empty;

  static inline const unsigned int test_head_nonempty = use_head_nonempty;

  static inline const unsigned int test_sum_init = use_sum_init;

  static inline const unsigned int test_nested = use_nested;

  static inline const unsigned int test_choose_true = use_choose_true;

  static inline const unsigned int test_choose_false = use_choose_false;
};
