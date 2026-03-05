#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

template <typename I, typename A>
concept Numeric = requires(A a0) {
  { I::to_nat(a0) } -> std::convertible_to<unsigned int>;
};
template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
};
template <typename I, typename A>
concept Ord = requires(A a0, A a1) {
  { I::leb(a1, a0) } -> std::convertible_to<bool>;
};

struct Typeclasses {
  struct numNat {
    static unsigned int to_nat(unsigned int n) { return n; }
  };
  static_assert(Numeric<numNat, unsigned int>);

  struct numBool {
    static unsigned int to_nat(bool b) {
      if (b) {
        return (0 + 1);
      } else {
        return 0;
      }
    }
  };
  static_assert(Numeric<numBool, bool>);

  template <typename _tcI0, typename T1> struct numOption {
    static unsigned int to_nat(std::optional<T1> o) {
      if (o.has_value()) {
        T1 x = *o;
        return (_tcI0::to_nat(x) + 1);
      } else {
        return 0;
      }
    }
  };

  template <typename _tcI0, typename T1> struct numList {
    static unsigned int to_nat(std::shared_ptr<List<T1>> a0) {
      std::function<unsigned int(std::shared_ptr<List<T1>>)> sum;
      sum = [&](std::shared_ptr<List<T1>> l) -> unsigned int {
        return std::visit(
            Overloaded{
                [](const typename List<T1>::nil _args) -> unsigned int {
                  return 0;
                },
                [&](const typename List<T1>::cons _args) -> unsigned int {
                  T1 x = _args._a0;
                  std::shared_ptr<List<T1>> rest = _args._a1;
                  return (_tcI0::to_nat(x) + sum(std::move(rest)));
                }},
            l->v());
      };
      return sum(a0);
    }
  };

  template <typename _tcI0, typename T1>
  static unsigned int numeric_sum(const std::shared_ptr<List<T1>> &l) {
    return numList<_tcI0, T1>::to_nat(l);
  }

  template <typename _tcI0, typename T1>
  static unsigned int numeric_double(const T1 x) {
    return (_tcI0::to_nat(x) + _tcI0::to_nat(x));
  }

  struct eqNat {
    static bool eqb(unsigned int a0, unsigned int a1) { return (a0 == a1); }
  };
  static_assert(Eq<eqNat, unsigned int>);

  struct ordNat {
    static bool leb(unsigned int a0, unsigned int a1) { return (a0 <= a1); }
  };
  static_assert(Ord<ordNat, unsigned int>);

  template <typename _tcI0, typename _tcI1, typename T1>
  static std::pair<T1, T1> sort_pair(const T1 x, const T1 y) {
    if (_tcI0::leb(x, y)) {
      return std::make_pair(x, y);
    } else {
      return std::make_pair(y, x);
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
  static T1 min_of(const T1 x, const T1 y) {
    if (_tcI0::leb(x, y)) {
      return x;
    } else {
      return y;
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
  static T1 max_of(const T1 x, const T1 y) {
    if (_tcI0::leb(x, y)) {
      return y;
    } else {
      return x;
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
  static unsigned int describe(const T1 x, const T1 y) {
    if (_tcI0::eqb(x, y)) {
      return _tcI1::to_nat(x);
    } else {
      return (_tcI1::to_nat(x) + _tcI1::to_nat(y));
    }
  }

  static inline const unsigned int test_nat = numNat::to_nat((
      (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1));

  static inline const unsigned int test_bool_true = numBool::to_nat(true);

  static inline const unsigned int test_bool_false = numBool::to_nat(false);

  static inline const unsigned int test_option_some =
      numOption<numNat, unsigned int>::to_nat(
          std::make_optional<unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1)));

  static inline const unsigned int test_option_none =
      numOption<numNat, unsigned int>::to_nat(std::nullopt);

  static inline const unsigned int test_list =
      numList<numNat, unsigned int>::to_nat(List<unsigned int>::ctor::cons_(
          (0 + 1),
          List<unsigned int>::ctor::cons_(
              ((0 + 1) + 1), List<unsigned int>::ctor::cons_(
                                 (((0 + 1) + 1) + 1),
                                 List<unsigned int>::ctor::cons_(
                                     ((((0 + 1) + 1) + 1) + 1),
                                     List<unsigned int>::ctor::nil_())))));

  static inline const unsigned int test_sum = numeric_sum<
      numNat, unsigned int>(List<unsigned int>::ctor::cons_(
      ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
      List<unsigned int>::ctor::cons_(
          ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1),
          List<unsigned int>::ctor::cons_(
              ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1),
              List<unsigned int>::ctor::nil_()))));

  static inline const unsigned int test_double =
      numeric_double<numNat, unsigned int>(
          (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  static inline const std::pair<unsigned int, unsigned int> test_sort_pair =
      sort_pair<ordNat, eqNat, unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1),
                                             (((0 + 1) + 1) + 1));

  static inline const unsigned int test_min =
      min_of<ordNat, eqNat, unsigned int>(
          ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          (((0 + 1) + 1) + 1));

  static inline const unsigned int test_max =
      max_of<ordNat, eqNat, unsigned int>(
          ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          (((0 + 1) + 1) + 1));

  static inline const unsigned int test_describe_eq =
      describe<eqNat, numNat, unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1),
                                            (((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_describe_ne =
      describe<eqNat, numNat, unsigned int>(
          (((0 + 1) + 1) + 1), (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
};
