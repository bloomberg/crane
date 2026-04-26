#ifndef INCLUDED_MATCH_REF_AFTER_MOVE
#define INCLUDED_MATCH_REF_AFTER_MOVE

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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct MatchRefAfterMove {
  /// This test exercises patterns where a value is destructured
  /// and then the original is also used, testing move/reference
  /// interactions in the generated C++.
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
        return mylist<t_A>(
            Mycons{clone_as_value<t_A>(d_a0),
                   clone_as_value<std::unique_ptr<mylist<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) mylist<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Mycons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<mylist<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist<t_A> mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0,
                                                    const mylist<t_A> &a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(a1.clone())});
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

    /// Pattern 1: Match on a list, return head AND apply a function
    /// to the tail that also takes the head as argument.
    /// The generated code must ensure h survives until both uses.
    __attribute__((pure)) unsigned int mylist_length() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return (1u + (*(d_a1)).mylist_length());
      }
    }

    template <typename T1, MapsTo<T1, t_A, mylist<t_A>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, mylist<t_A>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rect<T1>(f, f0));
      }
    }
  };

  template <typename t_A, typename t_B> struct mypair {
    // TYPES
    struct Mkpair {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Mkpair>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mypair() {}

    explicit mypair(Mkpair _v) : d_v_(std::move(_v)) {}

    mypair(const mypair<t_A, t_B> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    mypair(mypair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mypair<t_A, t_B> &
    operator=(const mypair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mypair<t_A, t_B> &
    operator=(mypair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mypair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Mkpair>(_sv.v());
      return mypair<t_A, t_B>(
          Mkpair{clone_as_value<t_A>(d_a0), clone_as_value<t_B>(d_a1)});
    }

    template <typename _CloneT0, typename _CloneT1>
    __attribute__((pure)) mypair<_CloneT0, _CloneT1> clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Mkpair>(_sv.v());
      return mypair<_CloneT0, _CloneT1>(
          typename mypair<_CloneT0, _CloneT1>::Mkpair{
              clone_as_value<_CloneT0>(d_a0), clone_as_value<_CloneT1>(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static mypair<t_A, t_B> mkpair(t_A a0, t_B a1) {
      return mypair(Mkpair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mypair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const mypair<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mypair<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 mypair_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename mypair<t_A, t_B>::Mkpair>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 mypair_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename mypair<t_A, t_B>::Mkpair>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  __attribute__((pure)) static mypair<unsigned int, unsigned int>
  head_and_tail_length(const mylist<unsigned int> &l);
  /// Pattern 2: Nested match where inner match is on a field of outer.
  /// After inner match, outer pattern variables are still used.
  ///
  /// BUG HYPOTHESIS: Outer match creates structured bindings into the
  /// outer value. Inner match on the tail might consume/move the tail.
  /// If the outer head h is a reference into the outer value, and
  /// the outer value is freed because the inner match consumes the
  /// tail (sole remaining reference), h dangles.
  __attribute__((pure)) static unsigned int
  nested_match_probe(const mylist<unsigned int> &l);
  /// Pattern 3: Build a pair where one element is from a match
  /// and the other is a function of the matched value.
  /// Tests evaluation order in pair construction.
  __attribute__((pure)) static mypair<unsigned int, mylist<unsigned int>>
  match_into_pair(const mylist<unsigned int> &l);
  /// Pattern 4: Double match on same value.
  /// First match extracts head, second match extracts tail.
  /// Between matches, the value might be moved.
  __attribute__((pure)) static mypair<unsigned int, mylist<unsigned int>>
  double_match(const mylist<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  mylist_sum(const mylist<unsigned int> &l);
  /// test1: head_and_tail_length 10,20,30 = (10, 2)
  static inline const unsigned int test1 = []() {
    auto &&_sv0 = head_and_tail_length(mylist<unsigned int>::mycons(
        10u, mylist<unsigned int>::mycons(
                 20u, mylist<unsigned int>::mycons(
                          30u, mylist<unsigned int>::mynil()))));
    const auto &[d_a00, d_a10] =
        std::get<typename mypair<unsigned int, unsigned int>::Mkpair>(_sv0.v());
    return (d_a00 + d_a10);
  }();
  /// test2: nested_match_probe 10,20,30 = 10+20+1 = 31
  static inline const unsigned int test2 =
      nested_match_probe(mylist<unsigned int>::mycons(
          10u, mylist<unsigned int>::mycons(
                   20u, mylist<unsigned int>::mycons(
                            30u, mylist<unsigned int>::mynil()))));
  /// test3: match_into_pair 5,10 = (5, 6,10)
  static inline const unsigned int test3 = []() {
    auto &&_sv1 = match_into_pair(mylist<unsigned int>::mycons(
        5u, mylist<unsigned int>::mycons(10u, mylist<unsigned int>::mynil())));
    const auto &[d_a01, d_a11] =
        std::get<typename mypair<unsigned int, mylist<unsigned int>>::Mkpair>(
            _sv1.v());
    return (d_a01 + mylist_sum(d_a11));
  }();
  /// test4: double_match 7,8,9 = (7, 8,9)
  static inline const unsigned int test4 = []() {
    auto &&_sv2 = double_match(mylist<unsigned int>::mycons(
        7u, mylist<unsigned int>::mycons(
                8u, mylist<unsigned int>::mycons(
                        9u, mylist<unsigned int>::mynil()))));
    const auto &[d_a02, d_a12] =
        std::get<typename mypair<unsigned int, mylist<unsigned int>>::Mkpair>(
            _sv2.v());
    return (d_a02 + mylist_sum(d_a12));
  }();

  /// Pattern 5: CPS with explicit continuation that captures from match.
  /// The continuation is a SIMPLE lambda, not a fixpoint.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  match_with_cont(const mylist<unsigned int> &l, F1 &&k) {
    if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(l.v())) {
      return k(0u, 0u);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename mylist<unsigned int>::Mycons>(l.v());
      return k(d_a0, (*(d_a1)).mylist_length());
    }
  }

  /// test5: match_with_cont 100, 200, 300 (+) = 100 + 2 = 102
  static inline const unsigned int test5 = match_with_cont(
      mylist<unsigned int>::mycons(
          100u, mylist<unsigned int>::mycons(
                    200u, mylist<unsigned int>::mycons(
                              300u, mylist<unsigned int>::mynil()))),
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      });

  /// Pattern 6: Deep nesting of matches with multiple constructors.
  template <typename t_A, typename t_B> struct either {
    // TYPES
    struct Left {
      t_A d_a0;
    };

    struct Right {
      t_B d_a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : d_v_(std::move(_v)) {}

    explicit either(Right _v) : d_v_(std::move(_v)) {}

    either(const either<t_A, t_B> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    either(either<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) either<t_A, t_B> &
    operator=(const either<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) either<t_A, t_B> &
    operator=(either<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) either<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return either<t_A, t_B>(Left{clone_as_value<t_A>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return either<t_A, t_B>(Right{clone_as_value<t_B>(d_a0)});
      }
    }

    template <typename _CloneT0, typename _CloneT1>
    __attribute__((pure)) either<_CloneT0, _CloneT1> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return either<_CloneT0, _CloneT1>(
            typename either<_CloneT0, _CloneT1>::Left{
                clone_as_value<_CloneT0>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return either<_CloneT0, _CloneT1>(
            typename either<_CloneT0, _CloneT1>::Right{
                clone_as_value<_CloneT1>(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static either<t_A, t_B> left(t_A a0) {
      return either(Left{std::move(a0)});
    }

    __attribute__((pure)) static either<t_A, t_B> right(t_B a0) {
      return either(Right{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) either<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const either<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = either<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either<t_A, t_B>::Left>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either<t_A, t_B>::Left>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  __attribute__((pure)) static unsigned int
  complex_match(const either<mylist<unsigned int>, mylist<unsigned int>> &e);
  /// test6: complex_match (Right 50, 60) = 50 + 1 = 51
  static inline const unsigned int test6 =
      complex_match(either<mylist<unsigned int>, mylist<unsigned int>>::right(
          mylist<unsigned int>::mycons(
              50u, mylist<unsigned int>::mycons(
                       60u, mylist<unsigned int>::mynil()))));
};

#endif // INCLUDED_MATCH_REF_AFTER_MOVE
