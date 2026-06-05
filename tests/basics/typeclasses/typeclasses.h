#ifndef INCLUDED_TYPECLASSES
#define INCLUDED_TYPECLASSES

#include <any>
#include <concepts>
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

template <typename I, typename A>
concept Numeric = requires(A a0) {
  { I::to_nat(a0) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a0, a1) } -> std::convertible_to<bool>;
};
template <typename I, typename A>
concept Ord = requires(A a0, A a1) {
  { I::leb(a0, a1) } -> std::convertible_to<bool>;
};

struct Typeclasses {
  struct numNat {
    static uint64_t to_nat(uint64_t n) { return n; }
  };

  static_assert(Numeric<numNat, uint64_t>);

  struct numBool {
    static uint64_t to_nat(bool b) {
      if (b) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(Numeric<numBool, bool>);

  template <typename _tcI0, typename T1> struct numOption {
    static uint64_t to_nat(std::optional<T1> o) {
      if (o.has_value()) {
        const T1 &x = *o;
        return (_tcI0::to_nat(x) + 1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  template <typename _tcI0, typename T1> struct numList {
    static uint64_t to_nat(List<T1> a0) {
      auto sum_impl = [&](auto &_self_sum, const List<T1> &l) -> uint64_t {
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a1, a2] = std::get<typename List<T1>::Cons>(l.v());
          return (_tcI0::to_nat(a1) + _self_sum(_self_sum, *a2));
        }
      };
      auto sum = [&](const List<T1> &l) -> uint64_t {
        return sum_impl(sum_impl, l);
      };
      return sum(a0);
    }
  };

  template <typename _tcI0, typename T1>
  static uint64_t numeric_sum(const List<T1> &l) {
    return numList<_tcI0, T1>::to_nat(l);
  }

  template <typename _tcI0, typename T1>
  static uint64_t numeric_double(const T1 &x) {
    return (_tcI0::to_nat(x) + _tcI0::to_nat(x));
  }

  struct eqNat {
    static bool eqb(uint64_t a0, uint64_t a1) { return a0 == a1; }
  };

  static_assert(Eq<eqNat, uint64_t>);

  struct ordNat {
    static bool leb(uint64_t a0, uint64_t a1) { return a0 <= a1; }
  };

  static_assert(Ord<ordNat, uint64_t>);

  template <typename _tcI0, typename _tcI1, typename T1>
  static std::pair<T1, T1> sort_pair(T1 x, T1 y) {
    if (_tcI0::leb(x, y)) {
      return std::make_pair(x, y);
    } else {
      return std::make_pair(std::move(y), x);
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
  static T1 min_of(T1 x, T1 y) {
    if (_tcI0::leb(x, y)) {
      return x;
    } else {
      return y;
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
  static T1 max_of(T1 x, T1 y) {
    if (_tcI0::leb(x, y)) {
      return y;
    } else {
      return x;
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
  static uint64_t describe(const T1 &x, const T1 &y) {
    if (_tcI0::eqb(x, y)) {
      return _tcI1::to_nat(x);
    } else {
      return (_tcI1::to_nat(x) + _tcI1::to_nat(y));
    }
  }

  static inline const uint64_t test_nat = numNat::to_nat(UINT64_C(42));
  static inline const uint64_t test_bool_true = numBool::to_nat(true);
  static inline const uint64_t test_bool_false = numBool::to_nat(false);
  static inline const uint64_t test_option_some =
      numOption<numNat, uint64_t>::to_nat(
          std::make_optional<uint64_t>(UINT64_C(5)));
  static inline const uint64_t test_option_none =
      numOption<numNat, uint64_t>::to_nat(std::optional<uint64_t>());
  static inline const uint64_t test_list =
      numList<numNat, uint64_t>::to_nat(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())))));
  static inline const uint64_t test_sum =
      numeric_sum<numNat, uint64_t>(List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))));
  static inline const uint64_t test_double =
      numeric_double<numNat, uint64_t>(UINT64_C(7));
  static inline const std::pair<uint64_t, uint64_t> test_sort_pair =
      sort_pair<ordNat, eqNat, uint64_t>(UINT64_C(5), UINT64_C(3));
  static inline const uint64_t test_min =
      min_of<ordNat, eqNat, uint64_t>(UINT64_C(8), UINT64_C(3));
  static inline const uint64_t test_max =
      max_of<ordNat, eqNat, uint64_t>(UINT64_C(8), UINT64_C(3));
  static inline const uint64_t test_describe_eq =
      describe<eqNat, numNat, uint64_t>(UINT64_C(5), UINT64_C(5));
  static inline const uint64_t test_describe_ne =
      describe<eqNat, numNat, uint64_t>(UINT64_C(3), UINT64_C(7));
};

#endif // INCLUDED_TYPECLASSES
