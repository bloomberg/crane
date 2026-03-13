#ifndef INCLUDED_IMPLICIT_ARGS
#define INCLUDED_IMPLICIT_ARGS

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

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::shared_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit mylist(Mynil _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mylist<t_A>> Mynil_() {
        return std::shared_ptr<mylist<t_A>>(new mylist<t_A>(Mynil{}));
      }

      static std::shared_ptr<mylist<t_A>>
      Mycons_(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
        return std::shared_ptr<mylist<t_A>>(new mylist<t_A>(Mycons{a0, a1}));
      }

      static std::unique_ptr<mylist<t_A>> Mynil_uptr() {
        return std::unique_ptr<mylist<t_A>>(new mylist<t_A>(Mynil{}));
      }

      static std::unique_ptr<mylist<t_A>>
      Mycons_uptr(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
        return std::unique_ptr<mylist<t_A>>(new mylist<t_A>(Mycons{a0, a1}));
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
            [&](const typename mylist<T1>::Mynil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::Mycons _args) -> T2 {
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
            [&](const typename mylist<T1>::Mynil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::Mycons _args) -> T2 {
              T1 y = _args.d_a0;
              std::shared_ptr<mylist<T1>> m0 = _args.d_a1;
              return f0(y, m0, mylist_rec<T1, T2>(f, f0, m0));
            }},
        m->v());
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  length(const std::shared_ptr<mylist<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename mylist<T1>::Mynil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename mylist<T1>::Mycons _args) -> unsigned int {
                     std::shared_ptr<mylist<T1>> rest = _args.d_a1;
                     return (1u + length<T1>(std::move(rest)));
                   }},
        l->v());
  }

  static inline const unsigned int explicit_id = id<unsigned int>(5u);
  static inline const unsigned int explicit_fst =
      fst_of<unsigned int, bool>(3u, true);
  __attribute__((pure)) static unsigned int add_one(const unsigned int _x0);
  __attribute__((pure)) static unsigned int double_nat(const unsigned int n);
  __attribute__((pure)) static unsigned int
  add_implicit(const unsigned int _x0, const unsigned int _x1);
  static inline const unsigned int use_add_implicit = add_implicit(5u, 3u);
  __attribute__((pure)) static unsigned int scale(const unsigned int _x0,
                                                  const unsigned int _x1);
  static inline const unsigned int use_scale = scale(3u, 7u);
  __attribute__((pure)) static unsigned int
  combine(const unsigned int a, const unsigned int b, const unsigned int x);
  static inline const unsigned int use_combine = combine(2u, 3u, 4u);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  apply_implicit(F0 &&f, const unsigned int _x0) {
    return f(std::move(_x0));
  }

  static inline const unsigned int use_apply_implicit = apply_implicit(
      [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 5u);
  __attribute__((pure)) static unsigned int with_base(const unsigned int _x0,
                                                      const unsigned int _x1);
  __attribute__((pure)) static unsigned int from_zero(const unsigned int _x0);
  __attribute__((pure)) static unsigned int from_ten(const unsigned int _x0);
  static inline const unsigned int use_from_zero = from_zero(5u);
  static inline const unsigned int use_from_ten = from_ten(5u);

  template <typename T1>
  static T1 head_or(const T1 default0, const std::shared_ptr<mylist<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename mylist<T1>::Mynil _args) -> T1 {
                     return default0;
                   },
                   [](const typename mylist<T1>::Mycons _args) -> T1 {
                     T1 x = _args.d_a0;
                     return x;
                   }},
        l->v());
  }

  static inline const unsigned int use_head_empty =
      head_or<unsigned int>(0u, mylist<unsigned int>::ctor::Mynil_());
  static inline const unsigned int use_head_nonempty =
      head_or<unsigned int>(0u, mylist<unsigned int>::ctor::Mycons_(
                                    7u, mylist<unsigned int>::ctor::Mynil_()));
  __attribute__((pure)) static unsigned int
  sum_with_init(const unsigned int init,
                const std::shared_ptr<mylist<unsigned int>> &l);
  static inline const unsigned int use_sum_init =
      sum_with_init(5u, mylist<unsigned int>::ctor::Mycons_(
                            1u, mylist<unsigned int>::ctor::Mycons_(
                                    2u, mylist<unsigned int>::ctor::Mynil_())));
  __attribute__((pure)) static unsigned int
  nested_implicits(const unsigned int a, const unsigned int b,
                   const unsigned int c);
  static inline const unsigned int use_nested = nested_implicits(1u, 2u, 3u);
  __attribute__((pure)) static unsigned int
  choose_branch(const bool flag, const unsigned int t, const unsigned int f);
  static inline const unsigned int use_choose_true =
      choose_branch(true, 7u, 3u);
  static inline const unsigned int use_choose_false =
      choose_branch(false, 7u, 3u);
  static inline const unsigned int test_id = id<unsigned int>(5u);
  static inline const unsigned int test_fst =
      fst_of<unsigned int, unsigned int>(3u, 7u);
  static inline const unsigned int test_apply =
      apply<unsigned int, unsigned int>(double_nat, 5u);
  static inline const unsigned int test_compose =
      compose<unsigned int, unsigned int, unsigned int>(
          double_nat,
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 3u);
  static inline const unsigned int test_length =
      length<unsigned int>(mylist<unsigned int>::ctor::Mycons_(
          1u, mylist<unsigned int>::ctor::Mycons_(
                  2u, mylist<unsigned int>::ctor::Mycons_(
                          3u, mylist<unsigned int>::ctor::Mynil_()))));
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

#endif // INCLUDED_IMPLICIT_ARGS
