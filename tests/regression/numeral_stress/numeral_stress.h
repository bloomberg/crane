#ifndef INCLUDED_NUMERAL_STRESS
#define INCLUDED_NUMERAL_STRESS

#include <any>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct NumeralStress {
  /// 1. Numeral inside option
  static inline const std::optional<uint64_t> opt_100 =
      std::make_optional<uint64_t>(UINT64_C(100));
  static inline const std::optional<int64_t> opt_neg =
      std::make_optional<int64_t>(INT64_C(-50)); /// 2. Numeral in a pair
  static inline const std::pair<uint64_t, int64_t> pair_nums =
      std::make_pair(UINT64_C(42), INT64_C(-7));
  /// 3. Numeral in a list
  static inline const List<int64_t> z_list = List<int64_t>::cons(
      INT64_C(1),
      List<int64_t>::cons(
          INT64_C(-2), List<int64_t>::cons(INT64_C(3), List<int64_t>::nil())));
  /// 4. Numeral as argument to Nat.add
  static inline const uint64_t add_big = (UINT64_C(1000) + UINT64_C(2000));
  /// 5. Numeral in match scrutinee
  static inline const uint64_t match_numeral = UINT64_C(1);
  /// 6. Numeral inside a fixpoint
  static uint64_t count_from(uint64_t n, uint64_t target);
  static inline const uint64_t test_count =
      count_from(UINT64_C(100), UINT64_C(50));
  /// 7. Z arithmetic with literals
  static inline const int64_t z_complex =
      ((INT64_C(100) * INT64_C(200)) + (INT64_C(50) - INT64_C(25)));

  /// 8. Multiple numerals in one record
  struct point {
    uint64_t px;
    uint64_t py;
  };

  static inline const point origin = point{UINT64_C(0), UINT64_C(0)};
  static inline const point far_point = point{UINT64_C(999), UINT64_C(888)};
  /// 9. Numeral in boolean expression
  static bool check_range(uint64_t n);
  static inline const bool test_range = check_range(UINT64_C(50));
  /// 10. Mixed nat and Z in one function
  static int64_t mixed_arith(uint64_t n);
  static inline const int64_t test_mixed = mixed_arith(UINT64_C(42));
};

#endif // INCLUDED_NUMERAL_STRESS
