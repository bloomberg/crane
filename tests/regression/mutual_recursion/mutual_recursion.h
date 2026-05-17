#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MutualRecursion {
  static bool even(unsigned int n);
  static bool odd(unsigned int n);
  static unsigned int sum_even_indices(unsigned int n, unsigned int acc);
  static unsigned int sum_odd_indices(unsigned int n, unsigned int acc);
  static unsigned int process_a(unsigned int n, unsigned int m);
  static unsigned int process_b(unsigned int n, unsigned int m);

  struct expr {
    // TYPES
    struct Val {
      unsigned int a0;
    };

    struct BinOp {
      unsigned int a0;
      std::unique_ptr<expr> a1;
      std::unique_ptr<expr> a2;
    };

    struct UnOp {
      unsigned int a0;
      std::unique_ptr<expr> a1;
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

    expr(const expr &_other) : v_(std::move(_other.clone().v_)) {}

    expr(expr &&_other) : v_(std::move(_other.v_)) {}

    expr &operator=(const expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    expr &operator=(expr &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    expr clone() const {
      expr _out{};

      struct _CloneFrame {
        const expr *_src;
        expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const expr *_src = _frame._src;
        expr *_dst = _frame._dst;
        if (std::holds_alternative<Val>(_src->v())) {
          const auto &_alt = std::get<Val>(_src->v());
          _dst->v_ = Val{_alt.a0};
        } else if (std::holds_alternative<BinOp>(_src->v())) {
          const auto &_alt = std::get<BinOp>(_src->v());
          _dst->v_ =
              BinOp{_alt.a0, _alt.a1 ? std::make_unique<expr>() : nullptr,
                    _alt.a2 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<BinOp>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        } else {
          const auto &_alt = std::get<UnOp>(_src->v());
          _dst->v_ =
              UnOp{_alt.a0, _alt.a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<UnOp>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static expr val(unsigned int a0) { return expr(Val{a0}); }

    static expr binop(unsigned int a0, expr a1, expr a2) {
      return expr(BinOp{a0, std::make_unique<expr>(std::move(a1)),
                        std::make_unique<expr>(std::move(a2))});
    }

    static expr unop(unsigned int a0, expr a1) {
      return expr(UnOp{a0, std::make_unique<expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::unique_ptr<expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<BinOp>(_node.v_)) {
          auto &_alt = std::get<BinOp>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
        if (std::holds_alternative<UnOp>(_node.v_)) {
          auto &_alt = std::get<UnOp>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &, expr &, T1 &,
                                   expr &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &, expr &, T1 &>
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
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &, expr &, T1 &,
                                   expr &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &, expr &, T1 &>
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

  static unsigned int eval_expr(const expr &e);
  static unsigned int f1(unsigned int n);
  static unsigned int f2(unsigned int n);
  static unsigned int f3(unsigned int n);
  static inline const bool test_even = even(10u);
  static inline const unsigned int test_sum = sum_even_indices(5u, 0u);
  static inline const unsigned int test_eval =
      eval_expr(expr::binop(0u, expr::val(5u), expr::val(10u)));
};

#endif // INCLUDED_MUTUAL_RECURSION
