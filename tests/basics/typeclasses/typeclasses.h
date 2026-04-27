#ifndef INCLUDED_TYPECLASSES
#define INCLUDED_TYPECLASSES

#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename I, typename t_A>
concept Numeric = requires(t_A a0) {
  { I::to_nat(a0) } -> std::convertible_to<unsigned int>;
};
template <typename I, typename t_A>
concept Eq = requires(t_A a0, t_A a1) {
  { I::eqb(a0, a1) } -> std::convertible_to<bool>;
};
template <typename I, typename t_A>
concept Ord = requires(t_A a0, t_A a1) {
  { I::leb(a0, a1) } -> std::convertible_to<bool>;
};

struct Typeclasses {
  struct numNat {
    __attribute__((pure)) static unsigned int to_nat(unsigned int n) {
      return n;
    }
  };

  static_assert(Numeric<numNat, unsigned int>);

  struct numBool {
    __attribute__((pure)) static unsigned int to_nat(bool b) {
      if (b) {
        return 1u;
      } else {
        return 0u;
      }
    }
  };

  static_assert(Numeric<numBool, bool>);

  template <typename _tcI0, typename T1> struct numOption {
    __attribute__((pure)) static unsigned int to_nat(std::optional<T1> o) {
      if (o.has_value()) {
        const T1 &x = *o;
        return (_tcI0::to_nat(x) + 1);
      } else {
        return 0u;
      }
    }
  };

  template <typename _tcI0, typename T1> struct numList {
    __attribute__((pure)) static unsigned int to_nat(List<T1> a0) {
      std::function<unsigned int(List<T1>)> sum;
      sum = [&](List<T1> l) -> unsigned int {
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          return 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          return (_tcI0::to_nat(d_a0) + sum(*(d_a1)));
        }
      };
      return sum(a0);
    }
  };

  template <typename _tcI0, typename T1>
  __attribute__((pure)) static unsigned int numeric_sum(const List<T1> &l) {
    return numList<_tcI0, T1>::to_nat(l);
  }

  template <typename _tcI0, typename T1>
  __attribute__((pure)) static unsigned int numeric_double(const T1 x) {
    return (_tcI0::to_nat(x) + _tcI0::to_nat(x));
  }

  struct eqNat {
    __attribute__((pure)) static bool eqb(unsigned int a0, unsigned int a1) {
      return a0 == a1;
    }
  };

  static_assert(Eq<eqNat, unsigned int>);

  struct ordNat {
    __attribute__((pure)) static bool leb(unsigned int a0, unsigned int a1) {
      return a0 <= a1;
    }
  };

  static_assert(Ord<ordNat, unsigned int>);

  template <typename _tcI0, typename _tcI1, typename T1>
  __attribute__((pure)) static std::pair<T1, T1> sort_pair(const T1 x,
                                                           const T1 y) {
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
  __attribute__((pure)) static unsigned int describe(const T1 x, const T1 y) {
    if (_tcI0::eqb(x, y)) {
      return _tcI1::to_nat(x);
    } else {
      return (_tcI1::to_nat(x) + _tcI1::to_nat(y));
    }
  }

  static inline const unsigned int test_nat = numNat::to_nat(42u);
  static inline const unsigned int test_bool_true = numBool::to_nat(true);
  static inline const unsigned int test_bool_false = numBool::to_nat(false);
  static inline const unsigned int test_option_some =
      numOption<numNat, unsigned int>::to_nat(
          std::make_optional<unsigned int>(5u));
  static inline const unsigned int test_option_none =
      numOption<numNat, unsigned int>::to_nat(std::optional<unsigned int>());
  static inline const unsigned int test_list =
      numList<numNat, unsigned int>::to_nat(List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::nil())))));
  static inline const unsigned int test_sum =
      numeric_sum<numNat, unsigned int>(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil()))));
  static inline const unsigned int test_double =
      numeric_double<numNat, unsigned int>(7u);
  static inline const std::pair<unsigned int, unsigned int> test_sort_pair =
      sort_pair<ordNat, eqNat, unsigned int>(5u, 3u);
  static inline const unsigned int test_min =
      min_of<ordNat, eqNat, unsigned int>(8u, 3u);
  static inline const unsigned int test_max =
      max_of<ordNat, eqNat, unsigned int>(8u, 3u);
  static inline const unsigned int test_describe_eq =
      describe<eqNat, numNat, unsigned int>(5u, 5u);
  static inline const unsigned int test_describe_ne =
      describe<eqNat, numNat, unsigned int>(3u, 7u);
};

#endif // INCLUDED_TYPECLASSES
