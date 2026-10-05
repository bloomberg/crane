#ifndef INCLUDED_REGISTER_PAIR_OPS
#define INCLUDED_REGISTER_PAIR_OPS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      A a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified forallb: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        _result = (f(a0) && std::move(_result));
      }
    }
    return _result;
  }
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct RegisterPairOps {
  template <typename T1>
  static List<T1> update_nth(uint64_t n, const T1 &x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state {
    List<uint64_t> regs;
  };

  static uint64_t get_reg(const state &s, uint64_t r);
  static state set_reg(const state &s, uint64_t r, uint64_t v);
  static uint64_t get_reg_pair(const state &s, uint64_t r);
  static state set_reg_pair(const state &s, uint64_t r, uint64_t v);
  static constexpr uint64_t test_get_reg_pair_even_value = UINT64_C(171);
  static inline const state sample_from_regs = state{List<uint64_t>::cons(
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(11),
                  List<uint64_t>::cons(
                      UINT64_C(0),
                      List<uint64_t>::cons(UINT64_C(0),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_get_reg_pair_from_regs = true;
  static constexpr bool test_get_reg_pair_odd_normalizes = true;
  static inline const state sample_pair_high = state{List<uint64_t>::cons(
      UINT64_C(2),
      List<uint64_t>::cons(
          UINT64_C(9),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(
                  UINT64_C(7),
                  List<uint64_t>::cons(
                      UINT64_C(8),
                      List<uint64_t>::cons(UINT64_C(1),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_set_reg_affects_pair_high = true;
  static inline const state sample_pair_low = state{List<uint64_t>::cons(
      UINT64_C(2),
      List<uint64_t>::cons(
          UINT64_C(9),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(
                  UINT64_C(7),
                  List<uint64_t>::cons(
                      UINT64_C(8),
                      List<uint64_t>::cons(UINT64_C(1),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_set_reg_affects_pair_low = true;
  static inline const state sample_idempotent = state{List<uint64_t>::cons(
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(0),
                  List<uint64_t>::cons(
                      UINT64_C(0),
                      List<uint64_t>::cons(UINT64_C(0),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_set_reg_pair_idempotent = true;
  static inline const state sample_preserves = state{List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(
                      UINT64_C(5),
                      List<uint64_t>::cons(UINT64_C(6),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_set_reg_pair_preserves_other_pairs = true;
  static uint64_t pair_base(uint64_t r);
  static inline const state sample_register_pair = state{List<uint64_t>::cons(
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(0),
                  List<uint64_t>::cons(
                      UINT64_C(0),
                      List<uint64_t>::cons(UINT64_C(0),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_even_projection = true;
  static constexpr bool test_odd_projection = true;
  static constexpr bool test_set_pair_get_high = true;
  static constexpr bool test_set_pair_get_low = true;
  static uint64_t pair_index(uint64_t r);
  static bool pair_property(uint64_t r);
  static inline const List<uint64_t> test_regs =
      ListDef::seq(UINT64_C(0), UINT64_C(16));
  static inline const bool test_register_pair_architecture =
      test_regs.forallb(pair_property);
  static inline const state sample_even_rounding = state{List<uint64_t>::cons(
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(UINT64_C(5),
                                           List<uint64_t>::nil()))))))};
  static constexpr uint64_t test_register_pair_even_rounding = UINT64_C(45);
  static inline const state sample_successor = state{List<uint64_t>::cons(
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(11),
                  List<uint64_t>::cons(
                      UINT64_C(0),
                      List<uint64_t>::cons(UINT64_C(0),
                                           List<uint64_t>::nil()))))))};
  static constexpr bool test_even_same_as_successor = true;
  static constexpr bool test_odd_same_as_predecessor = true;
  static inline const bool test_reg_pair_successor =
      (test_even_same_as_successor && test_odd_same_as_predecessor);
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<
                                      std::pair<
                                          std::pair<
                                              std::pair<
                                                  std::pair<uint64_t, bool>,
                                                  bool>,
                                              bool>,
                                          bool>,
                                      bool>,
                                  bool>,
                              bool>,
                          bool>,
                      bool>,
                  bool>,
              bool>,
          uint64_t>,
      bool>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(
                                                  std::make_pair(
                                                      std::make_pair(
                                                          test_get_reg_pair_even_value,
                                                          test_get_reg_pair_from_regs),
                                                      test_get_reg_pair_odd_normalizes),
                                                  test_set_reg_affects_pair_high),
                                              test_set_reg_affects_pair_low),
                                          test_set_reg_pair_idempotent),
                                      test_set_reg_pair_preserves_other_pairs),
                                  test_even_projection),
                              test_odd_projection),
                          test_set_pair_get_high),
                      test_set_pair_get_low),
                  test_register_pair_architecture),
              test_register_pair_even_rounding),
          test_reg_pair_successor);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, std::move(default0));
    }
  }
}

#endif // INCLUDED_REGISTER_PAIR_OPS
