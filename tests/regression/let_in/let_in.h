#ifndef INCLUDED_LET_IN
#define INCLUDED_LET_IN

#include <type_traits>
#include <utility>
#include <variant>

struct LetIn {
  static inline const unsigned int simple_let = 5u;
  static inline const unsigned int nested_let = 3u;
  static inline const unsigned int let_with_add = []() {
    unsigned int x = 3u;
    unsigned int y = 4u;
    return (x + y);
  }();
  static inline const unsigned int shadowed_let = 3u;
  static unsigned int let_in_fun(unsigned int n);
  static inline const unsigned int let_fun = []() {
    unsigned int x = 5u;
    return (x + 1u);
  }();

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

  static inline const unsigned int let_destruct = []() {
    pair<unsigned int, unsigned int> p =
        pair<unsigned int, unsigned int>::pair0(3u, 4u);
    auto &[a0, a1] =
        std::get<typename pair<unsigned int, unsigned int>::Pair0>(p.v_mut());
    return a0;
  }();
  static inline const unsigned int multi_let = []() {
    unsigned int a = 1u;
    unsigned int b = 2u;
    unsigned int c = 3u;
    return (a + (b + c));
  }();
  static inline const unsigned int test_simple = simple_let;
  static inline const unsigned int test_nested = nested_let;
  static inline const unsigned int test_add = let_with_add;
  static inline const unsigned int test_shadow = shadowed_let;
  static inline const unsigned int test_fun_call = let_in_fun(3u);
  static inline const unsigned int test_let_fun = let_fun;
  static inline const unsigned int test_destruct = let_destruct;
  static inline const unsigned int test_multi = multi_let;
};

#endif // INCLUDED_LET_IN
