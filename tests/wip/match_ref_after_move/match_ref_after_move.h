#ifndef INCLUDED_MATCH_REF_AFTER_MOVE
#define INCLUDED_MATCH_REF_AFTER_MOVE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct MatchRefAfterMove {
  /// This test exercises patterns where a value is destructured
  /// and then the original is also used, testing move/reference
  /// interactions in the generated C++.
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

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist<t_A>> mynil() {
      return std::make_shared<mylist<t_A>>(Mynil{});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_shared<mylist<t_A>>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_shared<mylist<t_A>>(
          Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Pattern 1: Match on a list, return head AND apply a function
    /// to the tail that also takes the head as argument.
    /// The generated code must ensure h survives until both uses.
    __attribute__((pure)) unsigned int mylist_length() const {
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(this->v());
        return (1u + d_a1->mylist_length());
      }
    }

    template <typename T1, MapsTo<T1, t_A, std::shared_ptr<mylist<t_A>>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, std::shared_ptr<mylist<t_A>>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rect<T1>(f, f0));
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
    explicit mypair(Mkpair _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mypair<t_A, t_B>> mkpair(t_A a0, t_B a1) {
      return std::make_shared<mypair<t_A, t_B>>(
          Mkpair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 mypair_rec(F0 &&f) const {
      const auto &[d_a0, d_a1] =
          std::get<typename mypair<t_A, t_B>::Mkpair>(this->v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 mypair_rect(F0 &&f) const {
      const auto &[d_a0, d_a1] =
          std::get<typename mypair<t_A, t_B>::Mkpair>(this->v());
      return f(d_a0, d_a1);
    }
  };

  static std::shared_ptr<mypair<unsigned int, unsigned int>>
  head_and_tail_length(const std::shared_ptr<mylist<unsigned int>> &l);
  /// Pattern 2: Nested match where inner match is on a field of outer.
  /// After inner match, outer pattern variables are still used.
  ///
  /// BUG HYPOTHESIS: Outer match creates structured bindings into the
  /// outer value. Inner match on the tail might consume/move the tail.
  /// If the outer head h is a reference into the outer value, and
  /// the outer value is freed because the inner match consumes the
  /// tail (sole remaining reference), h dangles.
  __attribute__((pure)) static unsigned int
  nested_match_probe(const std::shared_ptr<mylist<unsigned int>> &l);
  /// Pattern 3: Build a pair where one element is from a match
  /// and the other is a function of the matched value.
  /// Tests evaluation order in pair construction.
  static std::shared_ptr<
      mypair<unsigned int, std::shared_ptr<mylist<unsigned int>>>>
  match_into_pair(const std::shared_ptr<mylist<unsigned int>> &l);
  /// Pattern 4: Double match on same value.
  /// First match extracts head, second match extracts tail.
  /// Between matches, the value might be moved.
  static std::shared_ptr<
      mypair<unsigned int, std::shared_ptr<mylist<unsigned int>>>>
  double_match(const std::shared_ptr<mylist<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  mylist_sum(const std::shared_ptr<mylist<unsigned int>>
                 &l); /// test1: head_and_tail_length 10,20,30 = (10, 2)
  static inline const unsigned int test1 = []() {
    auto &&_sv0 = head_and_tail_length(mylist<unsigned int>::mycons(
        10u, mylist<unsigned int>::mycons(
                 20u, mylist<unsigned int>::mycons(
                          30u, mylist<unsigned int>::mynil()))));
    const auto &[d_a00, d_a10] =
        std::get<typename mypair<unsigned int, unsigned int>::Mkpair>(
            _sv0->v());
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
    const auto &[d_a01, d_a11] = std::get<typename mypair<
        unsigned int, std::shared_ptr<mylist<unsigned int>>>::Mkpair>(
        _sv1->v());
    return (d_a01 + mylist_sum(d_a11));
  }();
  /// test4: double_match 7,8,9 = (7, 8,9)
  static inline const unsigned int test4 = []() {
    auto &&_sv2 = double_match(mylist<unsigned int>::mycons(
        7u, mylist<unsigned int>::mycons(
                8u, mylist<unsigned int>::mycons(
                        9u, mylist<unsigned int>::mynil()))));
    const auto &[d_a02, d_a12] = std::get<typename mypair<
        unsigned int, std::shared_ptr<mylist<unsigned int>>>::Mkpair>(
        _sv2->v());
    return (d_a02 + mylist_sum(d_a12));
  }();

  /// Pattern 5: CPS with explicit continuation that captures from match.
  /// The continuation is a SIMPLE lambda, not a fixpoint.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  match_with_cont(const std::shared_ptr<mylist<unsigned int>> &l, F1 &&k) {
    if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(l->v())) {
      return k(0u, 0u);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename mylist<unsigned int>::Mycons>(l->v());
      return k(d_a0, d_a1->mylist_length());
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
    explicit either(Left _v) : d_v_(std::move(_v)) {}

    explicit either(Right _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<either<t_A, t_B>> left(t_A a0) {
      return std::make_shared<either<t_A, t_B>>(Left{std::move(a0)});
    }

    static std::shared_ptr<either<t_A, t_B>> right(t_B a0) {
      return std::make_shared<either<t_A, t_B>>(Right{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(this->v())) {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Left>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(this->v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(this->v())) {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Left>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(this->v());
        return f0(d_a0);
      }
    }
  };

  __attribute__((pure)) static unsigned int complex_match(
      const std::shared_ptr<either<std::shared_ptr<mylist<unsigned int>>,
                                   std::shared_ptr<mylist<unsigned int>>>> &e);
  /// test6: complex_match (Right 50, 60) = 50 + 1 = 51
  static inline const unsigned int test6 =
      complex_match(either<std::shared_ptr<mylist<unsigned int>>,
                           std::shared_ptr<mylist<unsigned int>>>::
                        right(mylist<unsigned int>::mycons(
                            50u, mylist<unsigned int>::mycons(
                                     60u, mylist<unsigned int>::mynil()))));
};

#endif // INCLUDED_MATCH_REF_AFTER_MOVE
