#ifndef INCLUDED_NUMERAL_EDGE
#define INCLUDED_NUMERAL_EDGE

#include <any>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct NumeralEdge {
  /// 1. Zero
  static inline const uint64_t nat_zero = UINT64_C(0);
  static inline const unsigned int n_zero = 0u;
  static inline const int64_t z_zero = INT64_C(0);
  /// 2. Small values
  static inline const uint64_t nat_one = UINT64_C(1);
  static inline const uint64_t nat_ten = UINT64_C(10);
  static inline const int64_t z_neg = INT64_C(-5);
  static inline const int64_t z_neg_one = INT64_C(-1);
  /// 3. Moderate values
  static inline const uint64_t nat_hundred = UINT64_C(100);
  static inline const int64_t z_thousand = INT64_C(1000);
  static inline const unsigned int n_large = 65535u;
  /// 4. Powers of 2
  static inline const uint64_t nat_pow2_8 = UINT64_C(256);
  static inline const uint64_t nat_pow2_16 = UINT64_C(65536);
  static inline const int64_t z_pow2_30 = INT64_C(1073741824);
  /// 5. Numerals in arithmetic expressions
  static inline const uint64_t add_numerals = (UINT64_C(100) + UINT64_C(200));
  static inline const int64_t mul_numerals = static_cast<int64_t>(
      static_cast<uint64_t>(INT64_C(10)) * static_cast<uint64_t>(INT64_C(20)));
  static inline const int64_t sub_numerals = static_cast<int64_t>(
      static_cast<uint64_t>(INT64_C(100)) - static_cast<uint64_t>(INT64_C(1)));
  /// 6. Numeral as function argument
  static uint64_t take_nat(uint64_t n);
  static inline const uint64_t test_arg = take_nat(UINT64_C(42));
  /// 7. Numeral in list
  static inline const List<uint64_t> nat_list = List<uint64_t>::cons(
      UINT64_C(1), List<uint64_t>::cons(
                       UINT64_C(2), List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil())));
  /// 8. Numeral in option
  static inline const std::optional<uint64_t> some_nat =
      std::make_optional<uint64_t>(UINT64_C(99));
  /// 9. Numeral in pair
  static inline const std::pair<uint64_t, uint64_t> nat_pair =
      std::make_pair(UINT64_C(10), UINT64_C(20));
  /// 10. Numeral in match
  static uint64_t classify(uint64_t n);
  /// 11. Comparison with numeral
  static bool is_big(uint64_t n);
  /// 12. Multiple Z values in one function
  static inline const int64_t z_arith =
      static_cast<int64_t>(static_cast<uint64_t>(INT64_C(10)) +
                           static_cast<uint64_t>(static_cast<int64_t>(
                               static_cast<uint64_t>(INT64_C(3)) *
                               static_cast<uint64_t>(INT64_C(7)))));
  /// 13. Negative Z in a pair
  static inline const std::pair<int64_t, int64_t> z_pair =
      std::make_pair(INT64_C(-42), INT64_C(42));
  /// 14. N conversion
  static inline const uint64_t n_to_nat_test = static_cast<unsigned int>(255u);
};

#endif // INCLUDED_NUMERAL_EDGE
