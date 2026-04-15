#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

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

  public:
    // CREATORS
    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(BinOp _v) : d_v_(std::move(_v)) {}

    explicit expr(UnOp _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<expr> val(unsigned int a0) {
      return std::make_shared<expr>(Val{std::move(a0)});
    }

    static std::shared_ptr<expr> binop(unsigned int a0,
                                       const std::shared_ptr<expr> &a1,
                                       const std::shared_ptr<expr> &a2) {
      return std::make_shared<expr>(BinOp{std::move(a0), a1, a2});
    }

    static std::shared_ptr<expr> binop(unsigned int a0,
                                       std::shared_ptr<expr> &&a1,
                                       std::shared_ptr<expr> &&a2) {
      return std::make_shared<expr>(
          BinOp{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::shared_ptr<expr> unop(unsigned int a0,
                                      const std::shared_ptr<expr> &a1) {
      return std::make_shared<expr>(UnOp{std::move(a0), a1});
    }

    static std::shared_ptr<expr> unop(unsigned int a0,
                                      std::shared_ptr<expr> &&a1) {
      return std::make_shared<expr>(UnOp{std::move(a0), std::move(a1)});
    }

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
    if (std::holds_alternative<typename expr::Val>(e->v())) {
      const auto &[d_a0] = std::get<typename expr::Val>(e->v());
      return f(d_a0);
    } else if (std::holds_alternative<typename expr::BinOp>(e->v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::BinOp>(e->v());
      return f0(d_a0, d_a1, expr_rect<T1>(f, f0, f4, d_a1), d_a2,
                expr_rect<T1>(f, f0, f4, d_a2));
    } else {
      const auto &[d_a0, d_a1] = std::get<typename expr::UnOp>(e->v());
      return f4(d_a0, d_a1, expr_rect<T1>(f, f0, f4, d_a1));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F1,
            MapsTo<T1, unsigned int, std::shared_ptr<expr>, T1> F2>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f4, const std::shared_ptr<expr> &e) {
    if (std::holds_alternative<typename expr::Val>(e->v())) {
      const auto &[d_a0] = std::get<typename expr::Val>(e->v());
      return f(d_a0);
    } else if (std::holds_alternative<typename expr::BinOp>(e->v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::BinOp>(e->v());
      return f0(d_a0, d_a1, expr_rec<T1>(f, f0, f4, d_a1), d_a2,
                expr_rec<T1>(f, f0, f4, d_a2));
    } else {
      const auto &[d_a0, d_a1] = std::get<typename expr::UnOp>(e->v());
      return f4(d_a0, d_a1, expr_rec<T1>(f, f0, f4, d_a1));
    }
  }

  __attribute__((pure)) static unsigned int
  eval_expr(const std::shared_ptr<expr> &e);
  __attribute__((pure)) static unsigned int f1(const unsigned int n);
  __attribute__((pure)) static unsigned int f2(const unsigned int n);
  __attribute__((pure)) static unsigned int f3(const unsigned int n);
  static inline const bool test_even = even(10u);
  static inline const unsigned int test_sum = sum_even_indices(5u, 0u);
  static inline const unsigned int test_eval =
      eval_expr(expr::binop(0u, expr::val(5u), expr::val(10u)));
};

#endif // INCLUDED_MUTUAL_RECURSION
