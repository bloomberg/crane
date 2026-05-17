#ifndef INCLUDED_CURRYING
#define INCLUDED_CURRYING

#include <type_traits>
#include <utility>
#include <variant>

struct Currying {
  static unsigned int add3(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int add3_partial1(unsigned int _x0, unsigned int _x1);
  static unsigned int add3_partial2(unsigned int _x0);

  template <typename A, typename B> struct pair {
    // TYPES
    struct Pair0 {
      A a0;
      B a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : v_(std::move(_v)) {}

    pair(const pair<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

    pair(pair<A, B> &&_other) : v_(std::move(_other.v_)) {}

    pair<A, B> &operator=(const pair<A, B> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    pair<A, B> &operator=(pair<A, B> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    pair<A, B> clone() const {
      const auto &[a0, a1] = std::get<Pair0>(this->v());
      return pair<A, B>(Pair0{a0, a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[a0, a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      this->v_ = Pair0{A(a0), B(a1)};
    }

    static pair<A, B> pair0(A a0, B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, pair<T1, T2> &>
  static T3 curry(F0 &&f, T1 a, T2 b) {
    return f(pair<T1, T2>::pair0(a, b));
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 uncurry(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(a0, a1);
  }

  static unsigned int pair_add(const pair<unsigned int, unsigned int> &p);
  static unsigned int curried_add(unsigned int _x0, unsigned int _x1);
  static unsigned int
  uncurried_add3(const pair<unsigned int, pair<unsigned int, unsigned int>> &p);

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 flip(F0 &&f, const T2 &b, const T1 &a) {
    return f(a, b);
  }

  static unsigned int sub(unsigned int _x0, unsigned int _x1);
  static unsigned int flipped_sub(unsigned int _x0, unsigned int _x1);
  static unsigned int add_base(unsigned int _x0, unsigned int _x1);
  static unsigned int add_ten(unsigned int _x0);
  static inline const unsigned int test_add3 = add3(1u, 2u, 3u);
  static inline const unsigned int test_partial1 = add3_partial1(2u, 3u);
  static inline const unsigned int test_partial2 = add3_partial2(3u);
  static inline const unsigned int test_curried = curried_add(3u, 4u);
  static inline const unsigned int test_flip = flipped_sub(3u, 7u);
  static inline const unsigned int test_add_ten = add_ten(5u);
};

#endif // INCLUDED_CURRYING
