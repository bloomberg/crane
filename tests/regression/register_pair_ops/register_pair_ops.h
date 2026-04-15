#ifndef INCLUDED_REGISTER_PAIR_OPS
#define INCLUDED_REGISTER_PAIR_OPS

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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return true;
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return (f(_m.d_a0) && _m.d_a1->forallb(f));
    }
  }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
        return _m.d_a0;
      }
    } else {
      unsigned int m = n - 1;
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &_m0 = *std::get_if<typename List<t_A>::Cons>(&this->v());
        return _m0.d_a1->nth(m, default0);
      }
    }
  }
};

struct ListDef {
  static std::shared_ptr<List<unsigned int>> seq(const unsigned int start,
                                                 const unsigned int len);
};

struct RegisterPairOps {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &_m = *std::get_if<typename List<T1>::Cons>(&l->v());
        return List<T1>::cons(x, _m.d_a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &_m0 = *std::get_if<typename List<T1>::Cons>(&l->v());
        return List<T1>::cons(_m0.d_a0, update_nth<T1>(n_, x, _m0.d_a1));
      }
    }
  }

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
  };

  __attribute__((pure)) static unsigned int
  get_reg(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<state> set_reg(const std::shared_ptr<state> &s,
                                        const unsigned int r,
                                        const unsigned int v);
  __attribute__((pure)) static unsigned int
  get_reg_pair(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<state> set_reg_pair(const std::shared_ptr<state> &s,
                                             const unsigned int r,
                                             const unsigned int v);
  static inline const unsigned int test_get_reg_pair_even_value = get_reg_pair(
      std::make_shared<state>(state{List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          10u, List<unsigned int>::cons(
                                   11u, List<unsigned int>::nil()))))}),
      2u);
  static inline const std::shared_ptr<state> sample_from_regs =
      std::make_shared<state>(state{List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          10u,
                          List<unsigned int>::cons(
                              11u,
                              List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil()))))))});
  static inline const bool test_get_reg_pair_from_regs =
      get_reg_pair(sample_from_regs, 2u) == 171u;
  static inline const bool test_get_reg_pair_odd_normalizes =
      get_reg_pair(
          std::make_shared<state>(state{List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      1u, List<unsigned int>::cons(
                              10u, List<unsigned int>::cons(
                                       11u, List<unsigned int>::nil()))))}),
          2u) ==
      get_reg_pair(
          std::make_shared<state>(state{List<unsigned int>::cons(
              0u, List<unsigned int>::cons(
                      1u, List<unsigned int>::cons(
                              10u, List<unsigned int>::cons(
                                       11u, List<unsigned int>::nil()))))}),
          3u);
  static inline const std::shared_ptr<state> sample_pair_high =
      std::make_shared<state>(state{List<unsigned int>::cons(
          2u,
          List<unsigned int>::cons(
              9u,
              List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  8u, List<unsigned int>::cons(
                                          1u, List<unsigned int>::nil()))))))});
  static inline const bool test_set_reg_affects_pair_high =
      get_reg_pair(set_reg(sample_pair_high, 2u, 13u), 2u) ==
      ((13u * 16u) + get_reg(sample_pair_high, 3u));
  static inline const std::shared_ptr<state> sample_pair_low =
      std::make_shared<state>(state{List<unsigned int>::cons(
          2u,
          List<unsigned int>::cons(
              9u,
              List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  8u, List<unsigned int>::cons(
                                          1u, List<unsigned int>::nil()))))))});
  static inline const bool test_set_reg_affects_pair_low =
      get_reg_pair(set_reg(sample_pair_low, 3u, 12u), 3u) ==
      ((get_reg(sample_pair_low, 2u) * 16u) + 12u);
  static inline const std::shared_ptr<state> sample_idempotent =
      std::make_shared<state>(state{List<unsigned int>::cons(
          0u,
          List<unsigned int>::cons(
              0u,
              List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil()))))))});
  static inline const bool test_set_reg_pair_idempotent =
      get_reg_pair(
          set_reg_pair(set_reg_pair(sample_idempotent, 2u, 34u), 2u, 171u),
          2u) == 171u;
  static inline const std::shared_ptr<state> sample_preserves =
      std::make_shared<state>(state{List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u,
              List<unsigned int>::cons(
                  3u, List<unsigned int>::cons(
                          4u, List<unsigned int>::cons(
                                  5u, List<unsigned int>::cons(
                                          6u, List<unsigned int>::nil()))))))});
  static inline const bool test_set_reg_pair_preserves_other_pairs =
      get_reg_pair(set_reg_pair(sample_preserves, 0u, 171u), 2u) ==
      get_reg_pair(sample_preserves, 2u);
  __attribute__((pure)) static unsigned int pair_base(const unsigned int r);
  static inline const std::shared_ptr<state> sample_register_pair =
      std::make_shared<state>(state{List<unsigned int>::cons(
          0u,
          List<unsigned int>::cons(
              0u,
              List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil()))))))});
  static inline const bool test_even_projection = pair_base(6u) == 6u;
  static inline const bool test_odd_projection = pair_base(7u) == 6u;
  static inline const bool test_set_pair_get_high =
      get_reg(set_reg_pair(sample_register_pair, 2u, 171u), 2u) == 10u;
  static inline const bool test_set_pair_get_low =
      get_reg(set_reg_pair(sample_register_pair, 2u, 171u), 3u) == 11u;
  __attribute__((pure)) static unsigned int pair_index(const unsigned int r);
  __attribute__((pure)) static bool pair_property(const unsigned int r);
  static inline const std::shared_ptr<List<unsigned int>> test_regs =
      ListDef::seq(0u, 16u);
  static inline const bool test_register_pair_architecture =
      test_regs->forallb(pair_property);
  static inline const std::shared_ptr<state> sample_even_rounding =
      std::make_shared<state>(state{List<unsigned int>::cons(
          0u,
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::cons(
                                          5u, List<unsigned int>::nil()))))))});
  static inline const unsigned int test_register_pair_even_rounding =
      get_reg_pair(set_reg_pair(sample_even_rounding, 3u, 45u), 3u);
  static inline const std::shared_ptr<state> sample_successor =
      std::make_shared<state>(state{List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          10u,
                          List<unsigned int>::cons(
                              11u,
                              List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil()))))))});
  static inline const bool test_even_same_as_successor =
      get_reg_pair(sample_successor, 2u) == get_reg_pair(sample_successor, 3u);
  static inline const bool test_odd_same_as_predecessor =
      get_reg_pair(sample_successor, 3u) == get_reg_pair(sample_successor, 2u);
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
                                                  std::pair<unsigned int, bool>,
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
          unsigned int>,
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

#endif // INCLUDED_REGISTER_PAIR_OPS
