#ifndef INCLUDED_INC_XCH_NIBBLE
#define INCLUDED_INC_XCH_NIBBLE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
};

struct IncXchNibble {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(x, d_a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, d_a10));
      }
    }
  }

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
    unsigned int acc;
  };

  __attribute__((pure)) static unsigned int
  get_reg(const std::shared_ptr<state> &s, const unsigned int r);
  __attribute__((pure)) static unsigned int nibble_of_nat(const unsigned int n);
  __attribute__((pure)) static unsigned int
  get_reg_pair(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<state> execute_inc(const std::shared_ptr<state> &s,
                                            const unsigned int r);
  static std::shared_ptr<state> execute_xch(const std::shared_ptr<state> &s,
                                            const unsigned int r);
  static inline const std::shared_ptr<state> sample = std::make_shared<state>(
      state{List<unsigned int>::cons(
                2u,
                List<unsigned int>::cons(
                    9u,
                    List<unsigned int>::cons(
                        4u,
                        List<unsigned int>::cons(
                            7u, List<unsigned int>::cons(
                                    8u, List<unsigned int>::cons(
                                            1u, List<unsigned int>::nil())))))),
            13u});
  static inline const bool inc_modifies_single_nibble_even =
      get_reg_pair(execute_inc(sample, 2u), 2u) ==
      ((nibble_of_nat((get_reg(sample, 2u) + 1u)) * 16u) + get_reg(sample, 3u));
  static inline const bool inc_modifies_single_nibble_odd =
      get_reg_pair(execute_inc(sample, 3u), 3u) ==
      ((get_reg(sample, 2u) * 16u) + nibble_of_nat((get_reg(sample, 3u) + 1u)));
  static inline const bool inc_preserves_pair_partner =
      get_reg(execute_inc(sample, 2u), 3u) == get_reg(sample, 3u);
  static inline const bool inc_preserves_pair_partner_odd =
      get_reg(execute_inc(sample, 3u), 2u) == get_reg(sample, 2u);
  static inline const bool xch_modifies_single_nibble_even =
      get_reg_pair(execute_xch(sample, 2u), 2u) ==
      ((nibble_of_nat(sample->acc) * 16u) + get_reg(sample, 3u));
  static inline const bool xch_modifies_single_nibble_odd =
      get_reg_pair(execute_xch(sample, 3u), 3u) ==
      ((get_reg(sample, 2u) * 16u) + nibble_of_nat(sample->acc));
  static inline const bool xch_preserves_pair_partner =
      get_reg(execute_xch(sample, 2u), 3u) == get_reg(sample, 3u);
  static inline const bool xch_preserves_pair_partner_odd =
      get_reg(execute_xch(sample, 3u), 2u) == get_reg(sample, 2u);
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
T1 ListDef::nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
      return ListDef::template nth<T1>(m, d_a10, default0);
    }
  }
}

#endif // INCLUDED_INC_XCH_NIBBLE
