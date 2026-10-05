#ifndef INCLUDED_UNIT_VOID_EDGE
#define INCLUDED_UNIT_VOID_EDGE

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

struct UnitVoidEdge {
  static void return_unit(uint64_t _x);
  static constexpr uint64_t let_bind_void_call = UINT64_C(42);
  static void count_down(uint64_t n);

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_unit_fn(F0 &&f, uint64_t x0_) {
    f(x0_);
    return;
  }

  template <typename F0> static uint64_t map_to_unit(F0 &&, uint64_t) {
    return UINT64_C(42);
  }

  template <typename T1> static T1 id(T1 x) { return x; }

  static constexpr std::monostate id_unit = std::monostate{};
  static void id_unit_fn(uint64_t _x);
  static constexpr uint64_t nested_lets = UINT64_C(42);
  static inline const std::optional<std::monostate> unit_some =
      std::make_optional<std::monostate>(std::monostate{});
  static inline const std::optional<std::monostate> unit_none =
      std::optional<std::monostate>();
  static uint64_t match_option_unit(const std::optional<std::monostate> &o);
  static std::optional<std::monostate> return_some_tt(uint64_t n);
  static void unit_chain(std::monostate u);
  static void helper_void(uint64_t _x);
  static uint64_t use_helper(uint64_t n);
  static uint64_t match_unit_nontail(std::monostate u);
  static void unit_to_unit_with_work(std::monostate u);
  static void seq_voids(uint64_t _x);
  static void conditional_unit(bool b);

  template <typename T1> static uint64_t poly_take(const T1 &) {
    return UINT64_C(42);
  }

  static constexpr uint64_t take_tt = UINT64_C(42);
  static inline const List<std::monostate> unit_list =
      List<std::monostate>::cons(
          std::monostate{}, List<std::monostate>::cons(
                                std::monostate{}, List<std::monostate>::nil()));
  static uint64_t double_match_unit(std::monostate u1, std::monostate u2);

  template <typename F0> static void apply_and_discard(F0 &&f, uint64_t x0_) {
    {
      apply_unit_fn(f, x0_);
      return;
    }
  }

  static constexpr std::monostate test_apply_discard = std::monostate{};

  struct tagged_nat {
    uint64_t tn_value;
    std::monostate tn_tag;
  };

  static tagged_nat make_tagged(uint64_t n);
  static uint64_t get_value(const tagged_nat &t);
  static constexpr uint64_t test_record_unit = UINT64_C(99);
  static void make_callback(uint64_t n, std::monostate _x);
  static constexpr std::monostate test_make_callback = std::monostate{};

  template <typename F0, typename F1>
  static void multi_void_callbacks(F0 &&, F1 &&, uint64_t, bool) {
    return;
  }

  static void dummy_bool_void(bool _x);
  static constexpr std::monostate test_multi_cb = std::monostate{};
  static constexpr uint64_t test_let_bind = UINT64_C(42);
  static constexpr std::monostate test_count_down = std::monostate{};
  static constexpr std::monostate test_apply = std::monostate{};
  static constexpr uint64_t test_map = UINT64_C(42);
  static constexpr uint64_t test_nested = UINT64_C(42);
  static constexpr uint64_t test_match_some = UINT64_C(1);
  static constexpr uint64_t test_match_none = UINT64_C(0);
  static inline const std::optional<std::monostate> test_return_some =
      return_some_tt(UINT64_C(1));
  static constexpr uint64_t test_use_helper = UINT64_C(7);
  static constexpr uint64_t test_match_nontail = UINT64_C(7);
  static constexpr uint64_t test_double_match = UINT64_C(99);
  static constexpr uint64_t test_take_tt = UINT64_C(42);
};

#endif // INCLUDED_UNIT_VOID_EDGE
