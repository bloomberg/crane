#ifndef INCLUDED_INC_XCH_NIBBLE
#define INCLUDED_INC_XCH_NIBBLE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       t_A x = _args.d_a0;
                       return x;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args) -> t_A {
                       std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                       return std::move(l_)->nth(m, default0);
                     }},
          this->v());
    }
  }
};

struct IncXchNibble {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args.d_a0;
                                     std::shared_ptr<List<T1>> ys = _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(ys)));
                                   }},
                        l->v());
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
  static std::shared_ptr<state> execute_inc(std::shared_ptr<state> s,
                                            const unsigned int r);
  static std::shared_ptr<state> execute_xch(std::shared_ptr<state> s,
                                            const unsigned int r);
  static inline const std::shared_ptr<state> sample = std::make_shared<state>(
      state{List<unsigned int>::ctor::Cons_(
                2u,
                List<unsigned int>::ctor::Cons_(
                    9u,
                    List<unsigned int>::ctor::Cons_(
                        4u,
                        List<unsigned int>::ctor::Cons_(
                            7u,
                            List<unsigned int>::ctor::Cons_(
                                8u,
                                List<unsigned int>::ctor::Cons_(
                                    1u, List<unsigned int>::ctor::Nil_())))))),
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

#endif // INCLUDED_INC_XCH_NIBBLE
