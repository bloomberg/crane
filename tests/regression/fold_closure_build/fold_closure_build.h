#ifndef INCLUDED_FOLD_CLOSURE_BUILD
#define INCLUDED_FOLD_CLOSURE_BUILD

#include <functional>
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

struct FoldClosureBuild {
  /// FOLD-BASED CLOSURE BUILDING
  ///
  /// BUG HYPOTHESIS: When a fold_left uses its accumulator function
  /// parameter to build closures, the closure for each iteration
  /// captures the fold's function parameter by &. If the fold
  /// function is inlined and the parameter dies after the fold
  /// call returns, the closures hold dangling references.
  ///
  /// This is different from existing wip tests because:
  /// 1. The closures are built INSIDE A FOLD, not in a direct recursive
  /// function
  /// 2. The fold CALLBACK captures pattern variables from the fold's
  /// own match expression, creating a nested scope issue
  /// 3. Multiple closures are chained through the fold, each
  /// depending on the previous one
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
  } /// Simple fold_left.

  template <typename T1, typename T2, MapsTo<T1, T1, T2> F0>
  static T1 fold_left(F0 &&f, const T1 acc, const mylist<T2> &l) {
    if (std::holds_alternative<typename mylist<T2>::Mynil>(l.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T2>::Mycons>(l.v());
      return fold_left<T1, T2>(f, f(acc, d_a0), *(d_a1));
    }
  }

  /// Pattern 1: Build a COMPOSED function via fold.
  /// Each step wraps the accumulator in a new closure.
  ///
  /// Equivalent to:
  /// compose_all 10, 20, 30 id
  /// = fold_left (fun acc h => fun x => acc(h + x)) id 10,20,30
  /// = fun x => id(10 + (20 + (30 + x)))
  /// = fun x => 60 + x
  ///
  /// The inner closure fun x => acc(h+x) captures acc (std::function)
  /// and h (unsigned int). If these are captured by =, safe. By &, dangles.
  __attribute__((pure)) static unsigned int
  compose_adders(const mylist<unsigned int> &l, const unsigned int &_x0);
  /// test1: compose_adders 10,20,30 7 = 67
  static inline const unsigned int test1 = compose_adders(
      mylist<unsigned int>::mycons(
          10u, mylist<unsigned int>::mycons(
                   20u, mylist<unsigned int>::mycons(
                            30u, mylist<unsigned int>::mynil()))),
      7u);
  /// Pattern 2: Store the composed function and call it TWICE.
  /// If the closure chain has dangling references, the second call
  /// might read clobbered stack memory.
  static inline const unsigned int test2 = []() {
    std::function<unsigned int(unsigned int)> f =
        [](unsigned int _x0) -> unsigned int {
      return compose_adders(mylist<unsigned int>::mycons(
                                5u, mylist<unsigned int>::mycons(
                                        10u, mylist<unsigned int>::mynil())),
                            _x0);
    };
    return (f(0u) + f(100u));
  }();
  /// Pattern 3: Fold producing a list of closures (not composing them).
  /// Each closure captures the list element from the fold iteration.
  __attribute__((pure)) static mylist<std::function<unsigned int(unsigned int)>>
  collect_adders(const mylist<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  apply_all(const mylist<std::function<unsigned int(unsigned int)>> &fns,
            const unsigned int &x); /// test3: collect_adders 10,20,30
  /// = (30+_), (20+_), (10+_)  (reversed by fold_left)
  /// apply_all with x=5: (30+5) + (20+5) + (10+5) = 75
  static inline const unsigned int test3 =
      apply_all(collect_adders(mylist<unsigned int>::mycons(
                    10u, mylist<unsigned int>::mycons(
                             20u, mylist<unsigned int>::mycons(
                                      30u, mylist<unsigned int>::mynil())))),
                5u);
  /// Pattern 4: Fold with a FIXPOINT as accumulator.
  /// The fixpoint captures both acc and h from the fold callback.
  ///
  /// BUG HYPOTHESIS: The fixpoint go uses & to capture acc and h.
  /// acc is the std::function accumulator from fold_left.
  /// h is the current list element.
  /// Both are locals in the fold callback's scope.
  /// When fold returns, these scopes are destroyed, but the
  /// final fixpoint (stored in the accumulator) still references them.
  __attribute__((pure)) static unsigned int
  compose_with_fix(const mylist<unsigned int> &l, const unsigned int &_x0);
  /// test4: compose_with_fix 10
  /// first iteration: acc=id, h=10
  /// go(x) = x + acc(h) = x + id(10) = x + 10
  /// test4 = go(5) = 5 + 10 = 15
  static inline const unsigned int test4 = compose_with_fix(
      mylist<unsigned int>::mycons(10u, mylist<unsigned int>::mynil()), 5u);
  /// test5: compose_with_fix 10, 20
  /// first: acc=id, h=10, go1(x) = x + id(10) = x + 10
  /// second: acc=go1, h=20, go2(x) = x + go1(20) = x + 30
  /// test5 = go2(7) = 7 + 30 = 37
  static inline const unsigned int test5 = compose_with_fix(
      mylist<unsigned int>::mycons(
          10u,
          mylist<unsigned int>::mycons(20u, mylist<unsigned int>::mynil())),
      7u);
};

#endif // INCLUDED_FOLD_CLOSURE_BUILD
