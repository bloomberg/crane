#ifndef INCLUDED_NUMERAL_STRESS
#define INCLUDED_NUMERAL_STRESS

#include <cstdint>
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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
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

struct NumeralStress {
  /// 1. Numeral inside option
  static inline const std::optional<unsigned int> opt_100 =
      std::make_optional<unsigned int>(100u);
  static inline const std::optional<int64_t> opt_neg =
      std::make_optional<int64_t>(INT64_C(-50)); /// 2. Numeral in a pair
  static inline const std::pair<unsigned int, int64_t> pair_nums =
      std::make_pair(42u, INT64_C(-7));
  /// 3. Numeral in a list
  static inline const List<int64_t> z_list = List<int64_t>::cons(
      INT64_C(1),
      List<int64_t>::cons(
          INT64_C(-2), List<int64_t>::cons(INT64_C(3), List<int64_t>::nil())));
  /// 4. Numeral as argument to Nat.add
  static inline const unsigned int add_big = (1000u + 2000u);
  /// 5. Numeral in match scrutinee
  static inline const unsigned int match_numeral = 1u;
  /// 6. Numeral inside a fixpoint
  __attribute__((pure)) static unsigned int
  count_from(unsigned int n, const unsigned int &target);
  static inline const unsigned int test_count = count_from(100u, 50u);
  /// 7. Z arithmetic with literals
  static inline const int64_t z_complex =
      ((INT64_C(100) * INT64_C(200)) + (INT64_C(50) - INT64_C(25)));

  /// 8. Multiple numerals in one record
  struct point {
    unsigned int px;
    unsigned int py;

    __attribute__((pure)) point *operator->() { return this; }

    __attribute__((pure)) const point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) point clone() const {
      return point{(*(this)).px, (*(this)).py};
    }
  };

  static inline const point origin = point{0u, 0u};
  static inline const point far_point = point{999u, 888u};
  /// 9. Numeral in boolean expression
  __attribute__((pure)) static bool check_range(const unsigned int &n);
  static inline const bool test_range = check_range(50u);
  /// 10. Mixed nat and Z in one function
  __attribute__((pure)) static int64_t mixed_arith(const unsigned int &n);
  static inline const int64_t test_mixed = mixed_arith(42u);
};

#endif // INCLUDED_NUMERAL_STRESS
