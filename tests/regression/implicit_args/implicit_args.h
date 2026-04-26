#ifndef INCLUDED_IMPLICIT_ARGS
#define INCLUDED_IMPLICIT_ARGS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct ImplicitArgs {
  template <typename T1> static T1 id(const T1 x) { return x; }

  template <typename T1, typename T2> static T1 fst_of(const T1 x, const T2) {
    return x;
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 apply(F0 &&f, const T1 _x0) {
    return f(_x0);
  }

  template <typename T1, typename T2 = void, typename T3, typename F0,
            typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<t_A>(Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<t_A>(Mycons{clone_value(d_a0), clone_value(d_a1)});
      }
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        d_v_ = Mycons{clone_as_value<t_A>(d_a0),
                      d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static mylist<t_A> mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0,
                                                    const mylist<t_A> &a1) {
      return mylist(Mycons{std::move(a0), std::make_unique<mylist<t_A>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> *operator->() { return this; }

    __attribute__((pure)) const mylist<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int length(const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return (1u + length<T1>(*(d_a1)));
    }
  }

  static inline const unsigned int explicit_id = id<unsigned int>(5u);
  static inline const unsigned int explicit_fst =
      fst_of<unsigned int, bool>(3u, true);
  __attribute__((pure)) static unsigned int add_one(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int double_nat(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  add_implicit(const unsigned int &_x0, const unsigned int &_x1);
  static inline const unsigned int use_add_implicit = add_implicit(5u, 3u);
  __attribute__((pure)) static unsigned int scale(const unsigned int &_x0,
                                                  const unsigned int &_x1);
  static inline const unsigned int use_scale = scale(3u, 7u);
  __attribute__((pure)) static unsigned int
  combine(const unsigned int &a, const unsigned int &b, const unsigned int &x);
  static inline const unsigned int use_combine = combine(2u, 3u, 4u);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int apply_implicit(F0 &&f,
                                                           unsigned int _x0) {
    return f(_x0);
  }

  static inline const unsigned int use_apply_implicit = apply_implicit(
      [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 5u);
  __attribute__((pure)) static unsigned int with_base(const unsigned int &_x0,
                                                      const unsigned int &_x1);
  __attribute__((pure)) static unsigned int from_zero(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int from_ten(const unsigned int &_x0);
  static inline const unsigned int use_from_zero = from_zero(5u);
  static inline const unsigned int use_from_ten = from_ten(5u);

  template <typename T1>
  static T1 head_or(const T1 default0, const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return d_a0;
    }
  }

  static inline const unsigned int use_head_empty =
      head_or<unsigned int>(0u, mylist<unsigned int>::mynil());
  static inline const unsigned int use_head_nonempty = head_or<unsigned int>(
      0u, mylist<unsigned int>::mycons(7u, mylist<unsigned int>::mynil()));
  __attribute__((pure)) static unsigned int
  sum_with_init(unsigned int init, const mylist<unsigned int> &l);
  static inline const unsigned int use_sum_init = sum_with_init(
      5u,
      mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(2u, mylist<unsigned int>::mynil())));
  __attribute__((pure)) static unsigned int
  nested_implicits(const unsigned int &a, const unsigned int &b,
                   const unsigned int &c);
  static inline const unsigned int use_nested = nested_implicits(1u, 2u, 3u);
  __attribute__((pure)) static unsigned int
  choose_branch(const bool &flag, unsigned int t, unsigned int f);
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
      length<unsigned int>(mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(
                  2u, mylist<unsigned int>::mycons(
                          3u, mylist<unsigned int>::mynil()))));
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
