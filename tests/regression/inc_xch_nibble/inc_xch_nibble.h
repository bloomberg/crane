#ifndef INCLUDED_INC_XCH_NIBBLE
#define INCLUDED_INC_XCH_NIBBLE

#include <any>
#include <memory>
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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct IncXchNibble {
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
    uint64_t acc;

    // ACCESSORS
    state clone() const { return state{this->regs, this->acc}; }
  };

  static uint64_t get_reg(const state &s, uint64_t r);
  static uint64_t nibble_of_nat(uint64_t n);
  static uint64_t get_reg_pair(const state &s, uint64_t r);
  static state execute_inc(const state &s, uint64_t r);
  static state execute_xch(const state &s, uint64_t r);
  static inline const state sample =
      state{List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(
                    UINT64_C(9),
                    List<uint64_t>::cons(
                        UINT64_C(4),
                        List<uint64_t>::cons(
                            UINT64_C(7),
                            List<uint64_t>::cons(
                                UINT64_C(8),
                                List<uint64_t>::cons(
                                    UINT64_C(1), List<uint64_t>::nil())))))),
            UINT64_C(13)};
  static inline const bool inc_modifies_single_nibble_even =
      get_reg_pair(execute_inc(sample, UINT64_C(2)), UINT64_C(2)) ==
      ((nibble_of_nat((get_reg(sample, UINT64_C(2)) + UINT64_C(1))) *
        UINT64_C(16)) +
       get_reg(sample, UINT64_C(3)));
  static inline const bool inc_modifies_single_nibble_odd =
      get_reg_pair(execute_inc(sample, UINT64_C(3)), UINT64_C(3)) ==
      ((get_reg(sample, UINT64_C(2)) * UINT64_C(16)) +
       nibble_of_nat((get_reg(sample, UINT64_C(3)) + UINT64_C(1))));
  static inline const bool inc_preserves_pair_partner =
      get_reg(execute_inc(sample, UINT64_C(2)), UINT64_C(3)) ==
      get_reg(sample, UINT64_C(3));
  static inline const bool inc_preserves_pair_partner_odd =
      get_reg(execute_inc(sample, UINT64_C(3)), UINT64_C(2)) ==
      get_reg(sample, UINT64_C(2));
  static inline const bool xch_modifies_single_nibble_even =
      get_reg_pair(execute_xch(sample, UINT64_C(2)), UINT64_C(2)) ==
      ((nibble_of_nat(sample.acc) * UINT64_C(16)) +
       get_reg(sample, UINT64_C(3)));
  static inline const bool xch_modifies_single_nibble_odd =
      get_reg_pair(execute_xch(sample, UINT64_C(3)), UINT64_C(3)) ==
      ((get_reg(sample, UINT64_C(2)) * UINT64_C(16)) +
       nibble_of_nat(sample.acc));
  static inline const bool xch_preserves_pair_partner =
      get_reg(execute_xch(sample, UINT64_C(2)), UINT64_C(3)) ==
      get_reg(sample, UINT64_C(3));
  static inline const bool xch_preserves_pair_partner_odd =
      get_reg(execute_xch(sample, UINT64_C(3)), UINT64_C(2)) ==
      get_reg(sample, UINT64_C(2));
  static inline const bool t = (((((((inc_modifies_single_nibble_even &&
                                      inc_modifies_single_nibble_odd) &&
                                     inc_preserves_pair_partner) &&
                                    inc_preserves_pair_partner_odd) &&
                                   xch_modifies_single_nibble_even) &&
                                  xch_modifies_single_nibble_odd) &&
                                 xch_preserves_pair_partner) &&
                                xch_preserves_pair_partner_odd);
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

#endif // INCLUDED_INC_XCH_NIBBLE
