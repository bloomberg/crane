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
};
