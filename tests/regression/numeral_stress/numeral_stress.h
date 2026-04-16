#ifndef INCLUDED_NUMERAL_STRESS
#define INCLUDED_NUMERAL_STRESS

#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

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
  static inline const std::shared_ptr<List<int64_t>> z_list =
      List<int64_t>::cons(
          INT64_C(1), List<int64_t>::cons(
                          INT64_C(-2), List<int64_t>::cons(
                                           INT64_C(3), List<int64_t>::nil())));
  /// 4. Numeral as argument to Nat.add
  static inline const unsigned int add_big = (1000u + 2000u);
  /// 5. Numeral in match scrutinee
  static inline const unsigned int match_numeral = 1u;
  /// 6. Numeral inside a fixpoint
  __attribute__((pure)) static unsigned int
  count_from(const unsigned int n, const unsigned int target);
  static inline const unsigned int test_count = count_from(100u, 50u);
  /// 7. Z arithmetic with literals
  static inline const int64_t z_complex =
      ((INT64_C(100) * INT64_C(200)) + (INT64_C(50) - INT64_C(25)));

  /// 8. Multiple numerals in one record
  struct point {
    unsigned int px;
    unsigned int py;
  };

  static inline const std::shared_ptr<point> origin =
      std::make_shared<point>(point{0u, 0u});
  static inline const std::shared_ptr<point> far_point =
      std::make_shared<point>(point{999u, 888u});
  /// 9. Numeral in boolean expression
  __attribute__((pure)) static bool check_range(const unsigned int n);
  static inline const bool test_range = check_range(50u);
  /// 10. Mixed nat and Z in one function
  __attribute__((pure)) static int64_t mixed_arith(const unsigned int n);
  static inline const int64_t test_mixed = mixed_arith(42u);
};

#endif // INCLUDED_NUMERAL_STRESS
