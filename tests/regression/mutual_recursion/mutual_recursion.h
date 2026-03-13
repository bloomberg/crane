#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct MutualRecursion {
  __attribute__((pure)) static bool even(const unsigned int n);
  __attribute__((pure)) static bool odd(const unsigned int n);
  __attribute__((pure)) static unsigned int
  sum_even_indices(const unsigned int n, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  sum_odd_indices(const unsigned int n, const unsigned int acc);
  __attribute__((pure)) static unsigned int process_a(const unsigned int n,
                                                      const unsigned int m);
  __attribute__((pure)) static unsigned int process_b(const unsigned int n,
                                                      const unsigned int m);

  struct expr {
    // TYPES
    struct Val {
      unsigned int d_a0;
    };

    struct BinOp {
      unsigned int d_a0;
      std::shared_ptr<expr> d_a1;
      std::shared_ptr<expr> d_a2;
    };

    struct UnOp {
      unsigned int d_a0;
      std::shared_ptr<expr> d_a1;
    };

    using variant_t = std::variant<Val, BinOp, UnOp>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(BinOp _v) : d_v_(std::move(_v)) {}

    explicit expr(UnOp _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<expr> Val_(unsigned int a0) {
        return std::shared_ptr<expr>(new expr(Val{a0}));
      }

      static std::shared_ptr<expr> BinOp_(unsigned int a0,
                                          const std::shared_ptr<expr> &a1,
                                          const std::shared_ptr<expr> &a2) {
        return std::shared_ptr<expr>(new expr(BinOp{a0, a1, a2}));
      }

      static std::shared_ptr<expr> UnOp_(unsigned int a0,
                                         const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(UnOp{a0, a1}));
      }

      static std::unique_ptr<expr> Val_uptr(unsigned int a0) {
        return std::unique_ptr<expr>(new expr(Val{a0}));
      }

      static std::unique_ptr<expr> BinOp_uptr(unsigned int a0,
                                              const std::shared_ptr<expr> &a1,
                                              const std::shared_ptr<expr> &a2) {
        return std::unique_ptr<expr>(new expr(BinOp{a0, a1, a2}));
      }

      static std::unique_ptr<expr> UnOp_uptr(unsigned int a0,
                                             const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(UnOp{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F1,
            MapsTo<T1, unsigned int, std::shared_ptr<expr>, T1> F2>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f4,
                      const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{[&](const typename expr::Val _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename expr::BinOp _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     std::shared_ptr<expr> e0 = _args.d_a1;
                     std::shared_ptr<expr> e1 = _args.d_a2;
                     return f0(std::move(n), e0, expr_rect<T1>(f, f0, f4, e0),
                               e1, expr_rect<T1>(f, f0, f4, e1));
                   },
                   [&](const typename expr::UnOp _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     std::shared_ptr<expr> e0 = _args.d_a1;
                     return f4(std::move(n), e0, expr_rect<T1>(f, f0, f4, e0));
                   }},
        e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F1,
            MapsTo<T1, unsigned int, std::shared_ptr<expr>, T1> F2>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f4, const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{[&](const typename expr::Val _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename expr::BinOp _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     std::shared_ptr<expr> e0 = _args.d_a1;
                     std::shared_ptr<expr> e1 = _args.d_a2;
                     return f0(std::move(n), e0, expr_rec<T1>(f, f0, f4, e0),
                               e1, expr_rec<T1>(f, f0, f4, e1));
                   },
                   [&](const typename expr::UnOp _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     std::shared_ptr<expr> e0 = _args.d_a1;
                     return f4(std::move(n), e0, expr_rec<T1>(f, f0, f4, e0));
                   }},
        e->v());
  }

  __attribute__((pure)) static unsigned int
  eval_expr(const std::shared_ptr<expr> &e);
  __attribute__((pure)) static unsigned int f1(const unsigned int n);
  __attribute__((pure)) static unsigned int f2(const unsigned int n);
  __attribute__((pure)) static unsigned int f3(const unsigned int n);
  static inline const bool test_even = even(10u);
  static inline const unsigned int test_sum = sum_even_indices(5u, 0u);
  static inline const unsigned int test_eval = eval_expr(
      expr::ctor::BinOp_(0u, expr::ctor::Val_(5u), expr::ctor::Val_(10u)));
};

#endif // INCLUDED_MUTUAL_RECURSION
