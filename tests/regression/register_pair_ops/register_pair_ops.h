#ifndef INCLUDED_REGISTER_PAIR_OPS
#define INCLUDED_REGISTER_PAIR_OPS

#include <any>
#include <memory>
#include <type_traits>
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return true;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (f(a0) && a1->forallb(f));
    }
  }
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct RegisterPairOps {
  template <typename T1>
  static List<T1> update_nth(uint64_t n, T1 x, const List<T1> &l) {
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
  static inline const uint64_t test_get_reg_pair_even_value = get_reg_pair(
      state{List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(10),
                  List<uint64_t>::cons(UINT64_C(11), List<uint64_t>::nil()))))},
      UINT64_C(2));
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
  static inline const bool test_get_reg_pair_from_regs =
      get_reg_pair(sample_from_regs, UINT64_C(2)) == UINT64_C(171);
  static inline const bool test_get_reg_pair_odd_normalizes =
      get_reg_pair(
          state{List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(1), List<uint64_t>::cons(
                                   UINT64_C(10),
                                   List<uint64_t>::cons(
                                       UINT64_C(11), List<uint64_t>::nil()))))},
          UINT64_C(2)) ==
      get_reg_pair(
          state{List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(1), List<uint64_t>::cons(
                                   UINT64_C(10),
                                   List<uint64_t>::cons(
                                       UINT64_C(11), List<uint64_t>::nil()))))},
          UINT64_C(3));
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
  static inline const bool test_set_reg_affects_pair_high =
      get_reg_pair(set_reg(sample_pair_high, UINT64_C(2), UINT64_C(13)),
                   UINT64_C(2)) ==
      ((UINT64_C(13) * UINT64_C(16)) + get_reg(sample_pair_high, UINT64_C(3)));
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
  static inline const bool test_set_reg_affects_pair_low =
      get_reg_pair(set_reg(sample_pair_low, UINT64_C(3), UINT64_C(12)),
                   UINT64_C(3)) ==
      ((get_reg(sample_pair_low, UINT64_C(2)) * UINT64_C(16)) + UINT64_C(12));
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
  static inline const bool test_set_reg_pair_idempotent =
      get_reg_pair(set_reg_pair(set_reg_pair(sample_idempotent, UINT64_C(2),
                                             UINT64_C(34)),
                                UINT64_C(2), UINT64_C(171)),
                   UINT64_C(2)) == UINT64_C(171);
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
  static inline const bool test_set_reg_pair_preserves_other_pairs =
      get_reg_pair(set_reg_pair(sample_preserves, UINT64_C(0), UINT64_C(171)),
                   UINT64_C(2)) == get_reg_pair(sample_preserves, UINT64_C(2));
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
  static inline const bool test_even_projection =
      pair_base(UINT64_C(6)) == UINT64_C(6);
  static inline const bool test_odd_projection =
      pair_base(UINT64_C(7)) == UINT64_C(6);
  static inline const bool test_set_pair_get_high =
      get_reg(set_reg_pair(sample_register_pair, UINT64_C(2), UINT64_C(171)),
              UINT64_C(2)) == UINT64_C(10);
  static inline const bool test_set_pair_get_low =
      get_reg(set_reg_pair(sample_register_pair, UINT64_C(2), UINT64_C(171)),
              UINT64_C(3)) == UINT64_C(11);
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
  static inline const uint64_t test_register_pair_even_rounding = get_reg_pair(
      set_reg_pair(sample_even_rounding, UINT64_C(3), UINT64_C(45)),
      UINT64_C(3));
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
  static inline const bool test_even_same_as_successor =
      get_reg_pair(sample_successor, UINT64_C(2)) ==
      get_reg_pair(sample_successor, UINT64_C(3));
  static inline const bool test_odd_same_as_predecessor =
      get_reg_pair(sample_successor, UINT64_C(3)) ==
      get_reg_pair(sample_successor, UINT64_C(2));
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
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_REGISTER_PAIR_OPS
