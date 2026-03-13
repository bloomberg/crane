#ifndef INCLUDED_ISZ_OPS
#define INCLUDED_ISZ_OPS

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

struct IszOps {
  __attribute__((pure)) static unsigned int nibble_of_nat(const unsigned int n);

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
  };

  __attribute__((pure)) static unsigned int
  get_reg(const std::shared_ptr<state> &s, const unsigned int r);
  __attribute__((pure)) static unsigned int
  cycles_isz(const std::shared_ptr<state> &s, const unsigned int r);
  static inline const unsigned int test_cycle_branch =
      cycles_isz(std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
                     15u, List<unsigned int>::ctor::Nil_())}),
                 0u);
  __attribute__((pure)) static unsigned int
  isz_iterations(const unsigned int v);
  static inline const unsigned int test_iterations_remaining =
      (isz_iterations(0u) + isz_iterations(12u));
  __attribute__((pure)) static bool isz_loops(const std::shared_ptr<state> &s,
                                              const unsigned int r);
  __attribute__((pure)) static bool
  isz_terminates(const std::shared_ptr<state> &s, const unsigned int r);
  static inline const unsigned int test_loop_flags = []() {
    return [](void) {
      std::shared_ptr<state> s =
          std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
              15u, List<unsigned int>::ctor::Cons_(
                       3u, List<unsigned int>::ctor::Nil_()))});
      return ([&](void) {
        if (isz_loops(s, 0u)) {
          return 1u;
        } else {
          return 0u;
        }
      }() +
              [&](void) {
                if (isz_terminates(s, 0u)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }());
    }();
  }();
  static inline const std::pair<std::pair<unsigned int, unsigned int>,
                                unsigned int>
      t = std::make_pair(
          std::make_pair(test_cycle_branch, test_iterations_remaining),
          test_loop_flags);
};

#endif // INCLUDED_ISZ_OPS
