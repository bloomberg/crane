#ifndef INCLUDED_TYPECLASSES
#define INCLUDED_TYPECLASSES

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I, typename A>
concept Numeric = requires {
  { I::to_nat(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A>
concept Eq = requires {
  { I::eqb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};
template <typename I, typename A>
concept Ord = requires {
  { I::leb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};

struct Typeclasses {
  struct numNat {
    constexpr static uint64_t to_nat(uint64_t n) { return n; }
  };

  static_assert(Numeric<numNat, uint64_t>);

  struct numBool {
    constexpr static uint64_t to_nat(bool b) {
      if (b) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(Numeric<numBool, bool>);

  template <typename _tcI0, typename T1>
    requires Numeric<_tcI0, T1>
  struct numOption {
    static uint64_t to_nat(std::optional<T1> o) {
      if (o.has_value()) {
        const T1 &x = *o;
        return (_tcI0::to_nat(x) + 1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  template <typename _tcI0, typename T1>
    requires Numeric<_tcI0, T1>
  struct numList {
    static uint64_t to_nat(List<T1> a0) {
      auto sum_impl = [&](auto &_self_sum, const List<T1> &l) -> uint64_t {
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a1, a2] = std::get<typename List<T1>::Cons>(l.v());
          return (_tcI0::to_nat(a1) + _self_sum(_self_sum, *a2));
        }
      };
      {
        const List<T1> &_lc1_l = a0;
        return sum_impl(sum_impl, _lc1_l);
      }
    }
  };

  template <typename _tcI0, typename T1>
    requires Numeric<_tcI0, T1>
  static uint64_t numeric_sum(const List<T1> &l) {
    return numList<_tcI0, T1>::to_nat(l);
  }

  template <typename _tcI0, typename T1>
    requires Numeric<_tcI0, T1>
  static uint64_t numeric_double(const T1 &x) {
    return (_tcI0::to_nat(x) + _tcI0::to_nat(x));
  }

  struct eqNat {
    constexpr static bool eqb(uint64_t a0, uint64_t a1) { return a0 == a1; }
  };

  static_assert(Eq<eqNat, uint64_t>);

  struct ordNat {
    constexpr static bool leb(uint64_t a0, uint64_t a1) { return a0 <= a1; }
  };

  static_assert(Ord<ordNat, uint64_t>);

  template <typename _tcI0, typename _tcI1, typename T1>
    requires Ord<_tcI0, T1> && Eq<_tcI1, T1>
  static std::pair<T1, T1> sort_pair(const T1 &x, const T1 &y) {
    if (_tcI0::leb(x, y)) {
      return std::make_pair(x, y);
    } else {
      return std::make_pair(y, x);
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
    requires Ord<_tcI0, T1> && Eq<_tcI1, T1>
  static T1 min_of(T1 x, T1 y) {
    if (_tcI0::leb(x, y)) {
      return x;
    } else {
      return y;
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
    requires Ord<_tcI0, T1> && Eq<_tcI1, T1>
  static T1 max_of(T1 x, T1 y) {
    if (_tcI0::leb(x, y)) {
      return y;
    } else {
      return x;
    }
  }

  template <typename _tcI0, typename _tcI1, typename T1>
    requires Eq<_tcI0, T1> && Numeric<_tcI1, T1>
  static uint64_t describe(const T1 &x, const T1 &y) {
    if (_tcI0::eqb(x, y)) {
      return _tcI1::to_nat(x);
    } else {
      return (_tcI1::to_nat(x) + _tcI1::to_nat(y));
    }
  }

  static constexpr uint64_t test_nat = UINT64_C(42);
  static constexpr uint64_t test_bool_true = UINT64_C(1);
  static constexpr uint64_t test_bool_false = UINT64_C(0);
  static constexpr uint64_t test_option_some = UINT64_C(6);
  static constexpr uint64_t test_option_none = UINT64_C(0);
  static constexpr uint64_t test_list = UINT64_C(10);
  static constexpr uint64_t test_sum = UINT64_C(60);
  static constexpr uint64_t test_double = UINT64_C(14);
  static inline const std::pair<uint64_t, uint64_t> test_sort_pair =
      sort_pair<ordNat, eqNat, uint64_t>(UINT64_C(5), UINT64_C(3));
  static constexpr uint64_t test_min = UINT64_C(3);
  static constexpr uint64_t test_max = UINT64_C(8);
  static constexpr uint64_t test_describe_eq = UINT64_C(5);
  static constexpr uint64_t test_describe_ne = UINT64_C(10);
};

#endif // INCLUDED_TYPECLASSES
