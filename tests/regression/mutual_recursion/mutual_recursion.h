#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MutualRecursion {
  static bool even(uint64_t n);
  static bool odd(uint64_t n);
  static uint64_t sum_even_indices(uint64_t n, uint64_t acc);
  static uint64_t sum_odd_indices(uint64_t n, uint64_t acc);
  static uint64_t process_a(uint64_t n, uint64_t m);
  static uint64_t process_b(uint64_t n, uint64_t m);

  struct expr {
    // TYPES
    struct Val {
      uint64_t a0;
    };

    struct BinOp {
      uint64_t a0;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    struct UnOp {
      uint64_t a0;
      std::shared_ptr<expr> a1;
    };

    using variant_t = std::variant<Val, BinOp, UnOp>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Val _v) : v_(std::move(_v)) {}

    explicit expr(BinOp _v) : v_(std::move(_v)) {}

    explicit expr(UnOp _v) : v_(std::move(_v)) {}

    static expr val(uint64_t a0) { return expr(Val{a0}); }

    static expr binop(uint64_t a0, expr a1, expr a2) {
      return expr(BinOp{a0, std::make_shared<expr>(std::move(a1)),
                        std::make_shared<expr>(std::move(a2))});
    }

    static expr unop(uint64_t a0, expr a1) {
      return expr(UnOp{a0, std::make_shared<expr>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, expr &, T1 &, expr &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, expr &, T1 &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f4, const expr &e) {
    if (std::holds_alternative<typename expr::Val>(e.v())) {
      const auto &[a0] = std::get<typename expr::Val>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::BinOp>(e.v())) {
      const auto &[a0, a1, a2] = std::get<typename expr::BinOp>(e.v());
      return f0(a0, *a1, expr_rect<T1>(f, f0, f4, *a1), *a2,
                expr_rect<T1>(f, f0, f4, *a2));
    } else {
      const auto &[a0, a1] = std::get<typename expr::UnOp>(e.v());
      return f4(a0, *a1, expr_rect<T1>(f, f0, f4, *a1));
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, expr &, T1 &, expr &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, expr &, T1 &>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f4, const expr &e) {
    if (std::holds_alternative<typename expr::Val>(e.v())) {
      const auto &[a0] = std::get<typename expr::Val>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::BinOp>(e.v())) {
      const auto &[a0, a1, a2] = std::get<typename expr::BinOp>(e.v());
      return f0(a0, *a1, expr_rec<T1>(f, f0, f4, *a1), *a2,
                expr_rec<T1>(f, f0, f4, *a2));
    } else {
      const auto &[a0, a1] = std::get<typename expr::UnOp>(e.v());
      return f4(a0, *a1, expr_rec<T1>(f, f0, f4, *a1));
    }
  }

  static uint64_t eval_expr(const expr &e);
  static uint64_t f1(uint64_t n);
  static uint64_t f2(uint64_t n);
  static uint64_t f3(uint64_t n);
  static inline const bool test_even = even(UINT64_C(10));
  static inline const uint64_t test_sum =
      sum_even_indices(UINT64_C(5), UINT64_C(0));
  static inline const uint64_t test_eval = eval_expr(expr::binop(
      UINT64_C(0), expr::val(UINT64_C(5)), expr::val(UINT64_C(10))));
};

#endif // INCLUDED_MUTUAL_RECURSION
