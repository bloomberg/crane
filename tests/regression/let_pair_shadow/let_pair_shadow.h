#ifndef INCLUDED_LET_PAIR_SHADOW
#define INCLUDED_LET_PAIR_SHADOW

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LetPairShadow {
  /// BUG: Two sequential let '(a, b) := f x destructurings of COMPUTED
  /// pair results in the same scope both generate the C++ temporary name
  /// _cs. The second declaration shadows the first, producing invalid
  /// C++ (redefinition error).
  ///
  /// Root cause: the pair-destructuring temporary _cs is not uniquified
  /// per destructuring site. Each let '(x, y) := expr where expr is
  /// a function call emits:
  /// auto _cs = expr;
  /// const T& x = _cs.first;
  /// const T& y = _cs.second;
  /// When two such destructurings appear in sequence, the second
  /// auto _cs = ... collides with the first.
  ///
  /// Note: simple variable RHS (let '(x,y) := p) does NOT create a
  /// temporary — it accesses p.first/p.second directly. The bug
  /// only fires when the RHS is a computed expression (function call,
  /// constructor application, etc.).
  ///
  /// This is a codegen/compilation-failure bug.
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

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

    mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist<t_A> &operator=(mylist<t_A> &&_other) {
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
        return mylist<t_A>(Mycons{
            d_a0,
            d_a1 ? std::make_unique<LetPairShadow::mylist<t_A>>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        d_v_ = Mycons{t_A(d_a0),
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

  __attribute__((pure)) static unsigned int
  mylist_sum(const mylist<unsigned int> &l);

  /// Pattern 1: map_accum — two sequential pair destructurings of
  /// function-call results in the same match branch.
  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<mylist<T2>, T3>
  map_accum(F0 &&f, const T3 acc, const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return std::make_pair(mylist<T2>::mynil(), acc);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      auto _cs = f(acc, d_a0);
      const T3 &new_acc = _cs.first;
      const T2 &y = _cs.second;
      auto _cs1 = map_accum<T1, T2, T3>(f, new_acc, *(d_a1));
      const mylist<T2> &rest = _cs1.first;
      const T3 &final_acc = _cs1.second;
      return std::make_pair(mylist<T2>::mycons(y, rest), final_acc);
    }
  }

  /// test1: map_accum with running sum.
  /// f(acc, x) = (acc+x, acc).
  /// map_accum f 0 10,20,30 = (0,10,30, 60)
  /// sum(list) + acc = 40 + 60 = 100
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = map_accum<unsigned int, unsigned int, unsigned int>(
        [](unsigned int s, const unsigned int &x) {
          return std::make_pair((s + x), s);
        },
        0u,
        mylist<unsigned int>::mycons(
            10u, mylist<unsigned int>::mycons(
                     20u, mylist<unsigned int>::mycons(
                              30u, mylist<unsigned int>::mynil()))));
    const mylist<unsigned int> &l = _cs.first;
    const unsigned int &acc = _cs.second;
    return (mylist_sum(l) + acc);
  }();
  /// Helper functions that return pairs (force temporary allocation).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  add_pair(const unsigned int &a, const unsigned int &b);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  sub_pair(const unsigned int &a, const unsigned int &b);
  /// Pattern 2: Two destructs of function-call results in top-level body.
  __attribute__((pure)) static unsigned int
  double_call_destruct(const unsigned int &a, const unsigned int &b,
                       const unsigned int &c, const unsigned int &d);
  /// test2: add_pair 3 4 = (7, 12), sub_pair 10 3 = (7, 13)
  /// 7 + 12 + 7 + 13 = 39
  static inline const unsigned int test2 =
      double_call_destruct(3u, 4u, 10u, 3u);
  /// Pattern 3: Three destructs of function-call results.
  __attribute__((pure)) static unsigned int
  triple_call_destruct(const unsigned int &a, const unsigned int &b,
                       const unsigned int &c, const unsigned int &d,
                       const unsigned int &e, const unsigned int &f);
  /// test3: add_pair 1 2 = (3,2), add_pair 3 4 = (7,12),
  /// add_pair 5 6 = (11,30).  3+2+7+12+11+30 = 65
  static inline const unsigned int test3 =
      triple_call_destruct(1u, 2u, 3u, 4u, 5u, 6u);
};

#endif // INCLUDED_LET_PAIR_SHADOW
