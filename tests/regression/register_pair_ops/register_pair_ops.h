#ifndef INCLUDED_REGISTER_PAIR_OPS
#define INCLUDED_REGISTER_PAIR_OPS

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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args) -> bool { return true; },
            [&](const typename List<t_A>::Cons _args) -> bool {
              t_A a = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return (f(a) && std::move(l0)->forallb(f));
            }},
        this->v());
  }

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

struct PeanoNat {
  __attribute__((pure)) static unsigned int sub(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool leb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool ltb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
  __attribute__((pure)) static unsigned int modulo(const unsigned int x,
                                                   const unsigned int y);
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
  };

  __attribute__((pure)) static unsigned int
  get_reg(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<state>
  set_reg(std::shared_ptr<state> s, const unsigned int r, const unsigned int v);
  __attribute__((pure)) static unsigned int
  get_reg_pair(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<state> set_reg_pair(const std::shared_ptr<state> &s,
                                             const unsigned int r,
                                             const unsigned int v);
  static inline const unsigned int test_get_reg_pair_even_value = get_reg_pair(
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          0u, List<unsigned int>::ctor::Cons_(
                  1u, List<unsigned int>::ctor::Cons_(
                          10u, List<unsigned int>::ctor::Cons_(
                                   11u, List<unsigned int>::ctor::Nil_()))))}),
      2u);
  static inline const std::shared_ptr<state> sample_from_regs =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          0u,
          List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  10u,
                  List<unsigned int>::ctor::Cons_(
                      11u,
                      List<unsigned int>::ctor::Cons_(
                          0u, List<unsigned int>::ctor::Cons_(
                                  0u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_get_reg_pair_from_regs =
      PeanoNat::eqb(get_reg_pair(sample_from_regs, 2u), 171u);
  static inline const bool test_get_reg_pair_odd_normalizes = PeanoNat::eqb(
      get_reg_pair(
          std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  1u, List<unsigned int>::ctor::Cons_(
                          10u, List<unsigned int>::ctor::Cons_(
                                   11u, List<unsigned int>::ctor::Nil_()))))}),
          2u),
      get_reg_pair(
          std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  1u, List<unsigned int>::ctor::Cons_(
                          10u, List<unsigned int>::ctor::Cons_(
                                   11u, List<unsigned int>::ctor::Nil_()))))}),
          3u));
  static inline const std::shared_ptr<state> sample_pair_high =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          2u,
          List<unsigned int>::ctor::Cons_(
              9u,
              List<unsigned int>::ctor::Cons_(
                  4u,
                  List<unsigned int>::ctor::Cons_(
                      7u,
                      List<unsigned int>::ctor::Cons_(
                          8u, List<unsigned int>::ctor::Cons_(
                                  1u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_set_reg_affects_pair_high =
      PeanoNat::eqb(get_reg_pair(set_reg(sample_pair_high, 2u, 13u), 2u),
                    ((13u * 16u) + get_reg(sample_pair_high, 3u)));
  static inline const std::shared_ptr<state> sample_pair_low =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          2u,
          List<unsigned int>::ctor::Cons_(
              9u,
              List<unsigned int>::ctor::Cons_(
                  4u,
                  List<unsigned int>::ctor::Cons_(
                      7u,
                      List<unsigned int>::ctor::Cons_(
                          8u, List<unsigned int>::ctor::Cons_(
                                  1u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_set_reg_affects_pair_low =
      PeanoNat::eqb(get_reg_pair(set_reg(sample_pair_low, 3u, 12u), 3u),
                    ((get_reg(sample_pair_low, 2u) * 16u) + 12u));
  static inline const std::shared_ptr<state> sample_idempotent =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          0u,
          List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  0u,
                  List<unsigned int>::ctor::Cons_(
                      0u,
                      List<unsigned int>::ctor::Cons_(
                          0u, List<unsigned int>::ctor::Cons_(
                                  0u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_set_reg_pair_idempotent = PeanoNat::eqb(
      get_reg_pair(
          set_reg_pair(set_reg_pair(sample_idempotent, 2u, 34u), 2u, 171u), 2u),
      171u);
  static inline const std::shared_ptr<state> sample_preserves =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          1u,
          List<unsigned int>::ctor::Cons_(
              2u,
              List<unsigned int>::ctor::Cons_(
                  3u,
                  List<unsigned int>::ctor::Cons_(
                      4u,
                      List<unsigned int>::ctor::Cons_(
                          5u, List<unsigned int>::ctor::Cons_(
                                  6u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_set_reg_pair_preserves_other_pairs =
      PeanoNat::eqb(get_reg_pair(set_reg_pair(sample_preserves, 0u, 171u), 2u),
                    get_reg_pair(sample_preserves, 2u));
  __attribute__((pure)) static unsigned int pair_base(const unsigned int r);
  static inline const std::shared_ptr<state> sample_register_pair =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          0u,
          List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  0u,
                  List<unsigned int>::ctor::Cons_(
                      0u,
                      List<unsigned int>::ctor::Cons_(
                          0u, List<unsigned int>::ctor::Cons_(
                                  0u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_even_projection =
      PeanoNat::eqb(pair_base(6u), 6u);
  static inline const bool test_odd_projection =
      PeanoNat::eqb(pair_base(7u), 6u);
  static inline const bool test_set_pair_get_high = PeanoNat::eqb(
      get_reg(set_reg_pair(sample_register_pair, 2u, 171u), 2u), 10u);
  static inline const bool test_set_pair_get_low = PeanoNat::eqb(
      get_reg(set_reg_pair(sample_register_pair, 2u, 171u), 3u), 11u);
  __attribute__((pure)) static unsigned int pair_index(const unsigned int r);
  __attribute__((pure)) static bool pair_property(const unsigned int r);
  static inline const std::shared_ptr<List<unsigned int>> test_regs =
      ListDef::seq(0u, 16u);
  static inline const bool test_register_pair_architecture =
      test_regs->forallb(pair_property);
  static inline const std::shared_ptr<state> sample_even_rounding =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          0u,
          List<unsigned int>::ctor::Cons_(
              1u,
              List<unsigned int>::ctor::Cons_(
                  2u,
                  List<unsigned int>::ctor::Cons_(
                      3u,
                      List<unsigned int>::ctor::Cons_(
                          4u, List<unsigned int>::ctor::Cons_(
                                  5u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const unsigned int test_register_pair_even_rounding =
      get_reg_pair(set_reg_pair(sample_even_rounding, 3u, 45u), 3u);
  static inline const std::shared_ptr<state> sample_successor =
      std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
          0u,
          List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  10u,
                  List<unsigned int>::ctor::Cons_(
                      11u,
                      List<unsigned int>::ctor::Cons_(
                          0u, List<unsigned int>::ctor::Cons_(
                                  0u, List<unsigned int>::ctor::Nil_()))))))});
  static inline const bool test_even_same_as_successor = PeanoNat::eqb(
      get_reg_pair(sample_successor, 2u), get_reg_pair(sample_successor, 3u));
  static inline const bool test_odd_same_as_predecessor = PeanoNat::eqb(
      get_reg_pair(sample_successor, 3u), get_reg_pair(sample_successor, 2u));
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
