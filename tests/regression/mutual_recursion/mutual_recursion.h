#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct MutualRecursion {
  static bool even(const unsigned int &n);
  static bool odd(const unsigned int &n);
  static unsigned int sum_even_indices(const unsigned int &n, unsigned int acc);
  static unsigned int sum_odd_indices(const unsigned int &n, unsigned int acc);
  static unsigned int process_a(const unsigned int &n, unsigned int m);
  static unsigned int process_b(const unsigned int &n, unsigned int m);

  struct expr {
    // TYPES
    struct Val {
      unsigned int d_a0;
    };

    struct BinOp {
      unsigned int d_a0;
      std::unique_ptr<expr> d_a1;
      std::unique_ptr<expr> d_a2;
    };

    struct UnOp {
      unsigned int d_a0;
      std::unique_ptr<expr> d_a1;
    };

    using variant_t = std::variant<Val, BinOp, UnOp>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(BinOp _v) : d_v_(std::move(_v)) {}

    explicit expr(UnOp _v) : d_v_(std::move(_v)) {}

    expr(const expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    expr(expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    expr &operator=(const expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    expr &operator=(expr &&_other) {
      d_v_ = std::move(_other.d_v_);
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
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const expr *_src = _frame._src;
        expr *_dst = _frame._dst;
        if (std::holds_alternative<Val>(_src->v())) {
          const auto &_alt = std::get<Val>(_src->v());
          _dst->d_v_ = Val{_alt.d_a0};
        } else if (std::holds_alternative<BinOp>(_src->v())) {
          const auto &_alt = std::get<BinOp>(_src->v());
          _dst->d_v_ =
              BinOp{_alt.d_a0, _alt.d_a1 ? std::make_unique<expr>() : nullptr,
                    _alt.d_a2 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<BinOp>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        } else {
          const auto &_alt = std::get<UnOp>(_src->v());
          _dst->d_v_ =
              UnOp{_alt.d_a0, _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<UnOp>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static expr val(unsigned int a0) { return expr(Val{std::move(a0)}); }

    static expr binop(unsigned int a0, expr a1, expr a2) {
      return expr(BinOp{std::move(a0), std::make_unique<expr>(std::move(a1)),
                        std::make_unique<expr>(std::move(a2))});
    }

    static expr unop(unsigned int a0, expr a1) {
      return expr(UnOp{std::move(a0), std::make_unique<expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::unique_ptr<expr>> _stack{};
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<BinOp>(_node.d_v_)) {
          auto &_alt = std::get<BinOp>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
          }
        }
        if (std::holds_alternative<UnOp>(_node.d_v_)) {
          auto &_alt = std::get<UnOp>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, expr, T1, expr, T1> F1,
            MapsTo<T1, unsigned int, expr, T1> F2>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f4, const expr &e) {
    if (std::holds_alternative<typename expr::Val>(e.v())) {
      const auto &[d_a0] = std::get<typename expr::Val>(e.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename expr::BinOp>(e.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::BinOp>(e.v());
      return f0(d_a0, *(d_a1), expr_rect<T1>(f, f0, f4, *(d_a1)), *(d_a2),
                expr_rect<T1>(f, f0, f4, *(d_a2)));
    } else {
      const auto &[d_a0, d_a1] = std::get<typename expr::UnOp>(e.v());
      return f4(d_a0, *(d_a1), expr_rect<T1>(f, f0, f4, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, expr, T1, expr, T1> F1,
            MapsTo<T1, unsigned int, expr, T1> F2>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f4, const expr &e) {
    if (std::holds_alternative<typename expr::Val>(e.v())) {
      const auto &[d_a0] = std::get<typename expr::Val>(e.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename expr::BinOp>(e.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::BinOp>(e.v());
      return f0(d_a0, *(d_a1), expr_rec<T1>(f, f0, f4, *(d_a1)), *(d_a2),
                expr_rec<T1>(f, f0, f4, *(d_a2)));
    } else {
      const auto &[d_a0, d_a1] = std::get<typename expr::UnOp>(e.v());
      return f4(d_a0, *(d_a1), expr_rec<T1>(f, f0, f4, *(d_a1)));
    }
  }

  static unsigned int eval_expr(const expr &e);
  static unsigned int f1(const unsigned int &n);
  static unsigned int f2(const unsigned int &n);
  static unsigned int f3(const unsigned int &n);
  static inline const bool test_even = even(10u);
  static inline const unsigned int test_sum = sum_even_indices(5u, 0u);
  static inline const unsigned int test_eval =
      eval_expr(expr::binop(0u, expr::val(5u), expr::val(10u)));
};

#endif // INCLUDED_MUTUAL_RECURSION
