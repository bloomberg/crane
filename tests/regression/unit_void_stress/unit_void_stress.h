#ifndef INCLUDED_UNIT_VOID_STRESS
#define INCLUDED_UNIT_VOID_STRESS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
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
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

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

struct UnitVoidStress {
  static void consume(uint64_t n);
  static void discard(uint64_t _x);
  static std::pair<uint64_t, std::monostate> pair_with_void_call(uint64_t n);
  static std::optional<std::monostate> some_void_call(uint64_t n);
  static inline const List<std::monostate> list_void_calls =
      List<std::monostate>::cons(
          []() {
            consume(UINT64_C(1));
            return std::monostate{};
          }(),
          List<std::monostate>::cons(
              []() {
                consume(UINT64_C(2));
                return std::monostate{};
              }(),
              List<std::monostate>::nil()));
  static void id_void_call(uint64_t x0_);
  static std::pair<uint64_t, std::monostate> pair_with_discard(uint64_t n);
  static void store_and_call(uint64_t x0_);
  static std::pair<uint64_t, std::monostate> pair_via_let(uint64_t n);
  static void cond_void(bool b, uint64_t n);
  static void match_nat_void(uint64_t n);
  static std::pair<std::pair<uint64_t, std::monostate>, uint64_t>
  nested_pair_void(uint64_t n);
  static std::optional<std::pair<uint64_t, std::monostate>>
  option_pair_void(uint64_t n);
  static std::pair<uint64_t, uint64_t> let_void_then_pair(uint64_t n);
  static uint64_t seq_voids_value(uint64_t _x);
  static uint64_t void_in_one_branch(bool b, uint64_t n);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<void, F0 &, const T1 &>
  static List<std::monostate> map_void(F0 &&f, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<std::monostate>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return List<std::monostate>::cons(
          [&]() {
            f(a0);
            return std::monostate{};
          }(),
          map_void<T1>(f, *a1));
    }
  }

  static inline const List<std::monostate> test_map_void = map_void<uint64_t>(
      discard, List<uint64_t>::cons(
                   UINT64_C(1),
                   List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())));

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static std::optional<std::monostate> apply_void_to_option(F0 &&f,
                                                            uint64_t n) {
    return std::make_optional<std::monostate>([&]() {
      f(n);
      return std::monostate{};
    }());
  }

  static inline const std::optional<std::monostate> test_apply_void_option =
      apply_void_to_option(discard, UINT64_C(42));
  static inline const std::optional<std::monostate> make_some_tt =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const List<std::monostate> make_unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static inline const std::pair<std::monostate, std::monostate> make_unit_pair =
      std::make_pair(std::monostate{}, std::monostate{});

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 apply_result(F0 &&f, uint64_t x0_) {
    return f(x0_);
  }

  static inline const std::monostate test_apply_result_void = []() {
    apply_result<std::monostate>(
        [](const uint64_t &_wa0) {
          consume(_wa0);
          return std::monostate{};
        },
        UINT64_C(5));
    return std::monostate{};
  }();

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static std::pair<uint64_t, T1> apply_in_pair(F0 &&f, uint64_t n) {
    return std::make_pair(n, f(n));
  }

  static inline const std::pair<uint64_t, std::monostate>
      test_apply_in_pair_void = apply_in_pair<std::monostate>(
          [](const uint64_t &_wa0) {
            consume(_wa0);
            return std::monostate{};
          },
          UINT64_C(5));
  static void even_void(uint64_t n);
  static void odd_void(uint64_t n);
  static inline const std::monostate test_mutual_void = []() {
    even_void(UINT64_C(10));
    return std::monostate{};
  }();
  static void match_opt_void(const std::optional<uint64_t> &o);
  static inline const std::monostate test_match_opt_void = []() {
    match_opt_void(std::make_optional<uint64_t>(UINT64_C(3)));
    return std::monostate{};
  }();
  static inline const std::pair<uint64_t, std::monostate> test_pair_void =
      pair_with_void_call(UINT64_C(5));
  static inline const std::optional<std::monostate> test_some_void =
      some_void_call(UINT64_C(3));
  static inline const std::pair<uint64_t, uint64_t> test_let_void =
      let_void_then_pair(UINT64_C(7));
  static inline const uint64_t test_seq = seq_voids_value(UINT64_C(10));
  static inline const uint64_t test_branch =
      void_in_one_branch(true, UINT64_C(5));
};

#endif // INCLUDED_UNIT_VOID_STRESS
