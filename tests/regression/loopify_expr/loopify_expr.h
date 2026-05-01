#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
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

struct LoopifyExpr {
  /// Simple expression ADT with multiple recursive constructors.
  struct expr {
    // TYPES
    struct Val {
      unsigned int d_a0;
    };

    struct Succ {
      std::unique_ptr<expr> d_a0;
    };

    struct Add {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct Mul {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct Cond {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
      std::unique_ptr<expr> d_a2;
    };

    using variant_t = std::variant<Val, Succ, Add, Mul, Cond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(Succ _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    explicit expr(Cond _v) : d_v_(std::move(_v)) {}

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
        } else if (std::holds_alternative<Succ>(_src->v())) {
          const auto &_alt = std::get<Succ>(_src->v());
          _dst->d_v_ = Succ{_alt.d_a0 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Succ>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
        } else if (std::holds_alternative<Add>(_src->v())) {
          const auto &_alt = std::get<Add>(_src->v());
          _dst->d_v_ = Add{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Add>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<Mul>(_src->v())) {
          const auto &_alt = std::get<Mul>(_src->v());
          _dst->d_v_ = Mul{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Mul>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<Cond>(_src->v());
          _dst->d_v_ = Cond{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<expr>() : nullptr,
                            _alt.d_a2 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Cond>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static expr val(unsigned int a0) { return expr(Val{std::move(a0)}); }

    static expr succ(expr a0) {
      return expr(Succ{std::make_unique<expr>(std::move(a0))});
    }

    static expr add(expr a0, expr a1) {
      return expr(Add{std::make_unique<expr>(std::move(a0)),
                      std::make_unique<expr>(std::move(a1))});
    }

    static expr mul(expr a0, expr a1) {
      return expr(Mul{std::make_unique<expr>(std::move(a0)),
                      std::make_unique<expr>(std::move(a1))});
    }

    static expr cond(expr a0, expr a1, expr a2) {
      return expr(Cond{std::make_unique<expr>(std::move(a0)),
                       std::make_unique<expr>(std::move(a1)),
                       std::make_unique<expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::unique_ptr<expr>> _stack{};
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<Succ>(_node.d_v_)) {
          auto &_alt = std::get<Succ>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
        }
        if (std::holds_alternative<Add>(_node.d_v_)) {
          auto &_alt = std::get<Add>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<Mul>(_node.d_v_)) {
          auto &_alt = std::get<Mul>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<Cond>(_node.d_v_)) {
          auto &_alt = std::get<Cond>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    expr simplify() const {
      const expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename expr::Val>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
        return expr::val(d_a0);
      } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
        return expr::succ((*(d_a0)).simplify());
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Val>(_sv0.v());
          if (d_a00 <= 0) {
            return (*(d_a1)).simplify();
          } else {
            unsigned int n0 = d_a00 - 1;
            expr s1 = expr::val((n0 + 1));
            auto &&_sv1 = (*(d_a1)).simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
              if (d_a01 <= 0) {
                return s1;
              } else {
                unsigned int n2 = d_a01 - 1;
                return expr::add(std::move(s1), expr::val((n2 + 1)));
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
              return expr::add(std::move(s1), expr::succ(*(d_a01)));
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Add>(_sv1.v());
              return expr::add(std::move(s1), expr::add(*(d_a01), *(d_a11)));
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Mul>(_sv1.v());
              return expr::add(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
            } else {
              const auto &[d_a01, d_a11, d_a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              return expr::add(std::move(s1),
                               expr::cond(*(d_a01), *(d_a11), *(d_a21)));
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*(d_a00));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*(d_a00), *(d_a10), *(d_a20));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        }
      } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Val>(_sv0.v());
          if (d_a00 <= 0) {
            return expr::val(0u);
          } else {
            unsigned int _x = d_a00 - 1;
            auto &&_sv1 = (*(d_a1)).simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
              if (d_a01 <= 0) {
                return expr::val(0u);
              } else {
                unsigned int n1 = d_a01 - 1;
                expr s2 = expr::val((n1 + 1));
                if (d_a00 == 1u) {
                  return s2;
                } else {
                  return expr::mul(expr::val(d_a00), std::move(s2));
                }
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
              expr s2 = expr::succ(*(d_a01));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), std::move(s2));
              }
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Add>(_sv1.v());
              expr s2 = expr::add(*(d_a01), *(d_a11));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), std::move(s2));
              }
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Mul>(_sv1.v());
              expr s2 = expr::mul(*(d_a01), *(d_a11));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), std::move(s2));
              }
            } else {
              const auto &[d_a01, d_a11, d_a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              expr s2 = expr::cond(*(d_a01), *(d_a11), *(d_a21));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), std::move(s2));
              }
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*(d_a00));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*(d_a00), *(d_a10), *(d_a20));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1),
                             expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::Cond>(_sv.v());
        return expr::cond((*(d_a0)).simplify(), (*(d_a1)).simplify(),
                          (*(d_a2)).simplify());
      }
    }

    /// size e counts total number of nodes.
    unsigned int size() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After3 {
        expr *_s0;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After5 {
        expr *_s0;
      };

      /// Intermediate: saves [_s0, _s1], dispatches next recursive call.
      struct _After6 {
        const expr *_s0;
        const expr *_s1;
      };

      /// Intermediate: saves [_result, _s1], dispatches next recursive call.
      struct _After7 {
        unsigned int _result;
        const expr *_s1;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine2 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine4 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine8 {
        unsigned int _result_0;
        unsigned int _result_1;
      };

      /// Continuation: saves across recursive call.
      struct _Resume1 {};

      using _Frame = std::variant<_Enter, _After3, _After5, _After6, _After7,
                                  _Combine2, _Combine4, _Combine8, _Resume1>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After3, _After5, _After6, _After7, _Combine2,
      /// _Combine4, _Combine8, _Resume1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = 1u;
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After3{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After5{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After6{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_Combine2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After5>(_frame)) {
          auto _f = std::move(std::get<_After5>(_frame));
          _stack.emplace_back(_Combine4{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After6>(_frame)) {
          auto _f = std::move(std::get<_After6>(_frame));
          _stack.emplace_back(_After7{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After7>(_frame)) {
          auto _f = std::move(std::get<_After7>(_frame));
          _stack.emplace_back(_Combine8{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine2>(_frame)) {
          auto _f = std::move(std::get<_Combine2>(_frame));
          _result = ((_result + _f._result) + 1);
        } else if (std::holds_alternative<_Combine4>(_frame)) {
          auto _f = std::move(std::get<_Combine4>(_frame));
          _result = ((_result + _f._result) + 1);
        } else if (std::holds_alternative<_Combine8>(_frame)) {
          auto _f = std::move(std::get<_Combine8>(_frame));
          _result = ((_result + (_f._result_1 + _f._result_0)) + 1);
        } else {
          auto _f = std::move(std::get<_Resume1>(_frame));
          _result = (_result + 1);
        }
      }
      return _result;
    }

    /// count_vals e counts the number of Val nodes.
    unsigned int count_vals() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After2 {
        expr *_s0;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After4 {
        expr *_s0;
      };

      /// Intermediate: saves [_s0, _s1], dispatches next recursive call.
      struct _After5 {
        const expr *_s0;
        const expr *_s1;
      };

      /// Intermediate: saves [_result, _s1], dispatches next recursive call.
      struct _After6 {
        unsigned int _result;
        const expr *_s1;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine3 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine7 {
        unsigned int _result_0;
        unsigned int _result_1;
      };

      using _Frame = std::variant<_Enter, _After2, _After4, _After5, _After6,
                                  _Combine1, _Combine3, _Combine7>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After4, _After5, _After6, _Combine1,
      /// _Combine3, _Combine7.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = 1u;
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After4{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After5{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(_Combine1{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine3{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After5>(_frame)) {
          auto _f = std::move(std::get<_After5>(_frame));
          _stack.emplace_back(_After6{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After6>(_frame)) {
          auto _f = std::move(std::get<_After6>(_frame));
          _stack.emplace_back(_Combine7{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = (_result + _f._result);
        } else if (std::holds_alternative<_Combine3>(_frame)) {
          auto _f = std::move(std::get<_Combine3>(_frame));
          _result = (_result + _f._result);
        } else {
          auto _f = std::move(std::get<_Combine7>(_frame));
          _result = (_result + (_f._result_1 + _f._result_0));
        }
      }
      return _result;
    }

    /// depth e computes expression depth.
    unsigned int depth() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After3 {
        expr *_s0;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After5 {
        expr *_s0;
      };

      /// Intermediate: saves [_s0, _s1], dispatches next recursive call.
      struct _After6 {
        const expr *_s0;
        const expr *_s1;
      };

      /// Intermediate: saves [_result, _s1], dispatches next recursive call.
      struct _After7 {
        unsigned int _result;
        const expr *_s1;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine2 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine4 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine8 {
        unsigned int _result_0;
        unsigned int _result_1;
      };

      /// Continuation: saves across recursive call.
      struct _Resume1 {};

      using _Frame = std::variant<_Enter, _After3, _After5, _After6, _After7,
                                  _Combine2, _Combine4, _Combine8, _Resume1>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After3, _After5, _After6, _After7, _Combine2,
      /// _Combine4, _Combine8, _Resume1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After3{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After5{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After6{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_Combine2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After5>(_frame)) {
          auto _f = std::move(std::get<_After5>(_frame));
          _stack.emplace_back(_Combine4{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After6>(_frame)) {
          auto _f = std::move(std::get<_After6>(_frame));
          _stack.emplace_back(_After7{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After7>(_frame)) {
          auto _f = std::move(std::get<_After7>(_frame));
          _stack.emplace_back(_Combine8{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine2>(_frame)) {
          auto _f = std::move(std::get<_Combine2>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        } else if (std::holds_alternative<_Combine4>(_frame)) {
          auto _f = std::move(std::get<_Combine4>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        } else if (std::holds_alternative<_Combine8>(_frame)) {
          auto _f = std::move(std::get<_Combine8>(_frame));
          _result =
              (std::max(_result, std::max(_f._result_1, _f._result_0)) + 1);
        } else {
          auto _f = std::move(std::get<_Resume1>(_frame));
          _result = (_result + 1);
        }
      }
      return _result;
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    unsigned int eval() const {
      const expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename expr::Val>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
        return ((*(d_a0)).eval() + 1);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
        return ((*(d_a0)).eval() + (*(d_a1)).eval());
      } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
        return ((*(d_a0)).eval() * (*(d_a1)).eval());
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::Cond>(_sv.v());
        if (0u < (*(d_a0)).eval()) {
          return (*(d_a1)).eval();
        } else {
          return (*(d_a2)).eval();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, expr &, T1 &, expr &, T1 &,
                                     expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After3 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After5 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After6 {
        const expr *_s0;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      /// Intermediate: saves [_result, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After7 {
        T1 _result;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine2 {
        T1 _result;
        expr _s1;
        expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine4 {
        T1 _result;
        expr _s1;
        expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine8 {
        T1 _result_0;
        T1 _result_1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      /// Continuation: saves [f0, _s1] across recursive call.
      struct _Resume1 {
        F1 f0;
        expr _s1;
      };

      using _Frame = std::variant<_Enter, _After3, _After5, _After6, _After7,
                                  _Combine2, _Combine4, _Combine8, _Resume1>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After3, _After5, _After6, _After7, _Combine2,
      /// _Combine4, _Combine8, _Resume1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume1{f0, *(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After3{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After5{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _After6{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(
              _Combine2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After5>(_frame)) {
          auto _f = std::move(std::get<_After5>(_frame));
          _stack.emplace_back(
              _Combine4{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After6>(_frame)) {
          auto _f = std::move(std::get<_After6>(_frame));
          _stack.emplace_back(_After7{_result, _f._s1, std::move(_f._s2),
                                      std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After7>(_frame)) {
          auto _f = std::move(std::get<_After7>(_frame));
          _stack.emplace_back(_Combine8{_f._result, _result, std::move(_f._s2),
                                        std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine2>(_frame)) {
          auto _f = std::move(std::get<_Combine2>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._result);
        } else if (std::holds_alternative<_Combine4>(_frame)) {
          auto _f = std::move(std::get<_Combine4>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._result);
        } else if (std::holds_alternative<_Combine8>(_frame)) {
          auto _f = std::move(std::get<_Combine8>(_frame));
          _result =
              f3(_f._s4, _result, _f._s3, _f._result_1, _f._s2, _f._result_0);
        } else {
          auto _f = std::move(std::get<_Resume1>(_frame));
          _result = _f.f0(_f._s1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, expr &, T1 &, expr &, T1 &,
                                     expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After3 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After5 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After6 {
        const expr *_s0;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      /// Intermediate: saves [_result, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After7 {
        T1 _result;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine2 {
        T1 _result;
        expr _s1;
        expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine4 {
        T1 _result;
        expr _s1;
        expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine8 {
        T1 _result_0;
        T1 _result_1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      /// Continuation: saves [f0, _s1] across recursive call.
      struct _Resume1 {
        F1 f0;
        expr _s1;
      };

      using _Frame = std::variant<_Enter, _After3, _After5, _After6, _After7,
                                  _Combine2, _Combine4, _Combine8, _Resume1>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After3, _After5, _After6, _After7, _Combine2,
      /// _Combine4, _Combine8, _Resume1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume1{f0, *(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After3{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After5{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _After6{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(
              _Combine2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After5>(_frame)) {
          auto _f = std::move(std::get<_After5>(_frame));
          _stack.emplace_back(
              _Combine4{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After6>(_frame)) {
          auto _f = std::move(std::get<_After6>(_frame));
          _stack.emplace_back(_After7{_result, _f._s1, std::move(_f._s2),
                                      std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After7>(_frame)) {
          auto _f = std::move(std::get<_After7>(_frame));
          _stack.emplace_back(_Combine8{_f._result, _result, std::move(_f._s2),
                                        std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine2>(_frame)) {
          auto _f = std::move(std::get<_Combine2>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._result);
        } else if (std::holds_alternative<_Combine4>(_frame)) {
          auto _f = std::move(std::get<_Combine4>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._result);
        } else if (std::holds_alternative<_Combine8>(_frame)) {
          auto _f = std::move(std::get<_Combine8>(_frame));
          _result =
              f3(_f._s4, _result, _f._s3, _f._result_1, _f._s2, _f._result_0);
        } else {
          auto _f = std::move(std::get<_Resume1>(_frame));
          _result = _f.f0(_f._s1, _result);
        }
      }
      return _result;
    }
  };

  /// Alternative expression type for testing different evaluation strategy.
  struct simple_expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Plus {
      std::unique_ptr<simple_expr> d_a0;
      std::unique_ptr<simple_expr> d_a1;
    };

    struct IfPos {
      std::unique_ptr<simple_expr> d_a0;
      std::unique_ptr<simple_expr> d_a1;
      std::unique_ptr<simple_expr> d_a2;
    };

    using variant_t = std::variant<Lit, Plus, IfPos>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    simple_expr() {}

    explicit simple_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(IfPos _v) : d_v_(std::move(_v)) {}

    simple_expr(const simple_expr &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    simple_expr(simple_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    simple_expr &operator=(const simple_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    simple_expr &operator=(simple_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    simple_expr clone() const {
      simple_expr _out{};

      struct _CloneFrame {
        const simple_expr *_src;
        simple_expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const simple_expr *_src = _frame._src;
        simple_expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->d_v_ = Lit{_alt.d_a0};
        } else if (std::holds_alternative<Plus>(_src->v())) {
          const auto &_alt = std::get<Plus>(_src->v());
          _dst->d_v_ =
              Plus{_alt.d_a0 ? std::make_unique<simple_expr>() : nullptr,
                   _alt.d_a1 ? std::make_unique<simple_expr>() : nullptr};
          auto &_dst_alt = std::get<Plus>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<IfPos>(_src->v());
          _dst->d_v_ =
              IfPos{_alt.d_a0 ? std::make_unique<simple_expr>() : nullptr,
                    _alt.d_a1 ? std::make_unique<simple_expr>() : nullptr,
                    _alt.d_a2 ? std::make_unique<simple_expr>() : nullptr};
          auto &_dst_alt = std::get<IfPos>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static simple_expr lit(unsigned int a0) {
      return simple_expr(Lit{std::move(a0)});
    }

    static simple_expr plus(simple_expr a0, simple_expr a1) {
      return simple_expr(Plus{std::make_unique<simple_expr>(std::move(a0)),
                              std::make_unique<simple_expr>(std::move(a1))});
    }

    static simple_expr ifpos(simple_expr a0, simple_expr a1, simple_expr a2) {
      return simple_expr(IfPos{std::make_unique<simple_expr>(std::move(a0)),
                               std::make_unique<simple_expr>(std::move(a1)),
                               std::make_unique<simple_expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~simple_expr() {
      std::vector<std::unique_ptr<simple_expr>> _stack{};
      auto _drain = [&](simple_expr &_node) {
        if (std::holds_alternative<Plus>(_node.d_v_)) {
          auto &_alt = std::get<Plus>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<IfPos>(_node.d_v_)) {
          auto &_alt = std::get<IfPos>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    /// depth_simple e computes depth of simple expression tree.
    unsigned int depth_simple() const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After2 {
        simple_expr *_s0;
      };

      /// Intermediate: saves [_s0, _s1], dispatches next recursive call.
      struct _After3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
      };

      /// Intermediate: saves [_result, _s1], dispatches next recursive call.
      struct _After4 {
        unsigned int _result;
        const simple_expr *_s1;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine5 {
        unsigned int _result_0;
        unsigned int _result_1;
      };

      using _Frame =
          std::variant<_Enter, _After2, _After3, _After4, _Combine1, _Combine5>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After3, _After4, _Combine1,
      /// _Combine5.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_After3{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(_Combine1{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_After4{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine5{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        } else {
          auto _f = std::move(std::get<_Combine5>(_frame));
          _result =
              (std::max(_result, std::max(_f._result_1, _f._result_0)) + 1);
        }
      }
      return _result;
    }

    /// eval_simple e evaluates simple expression with positive test.
    unsigned int eval_simple() const {
      const simple_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename simple_expr::Lit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename simple_expr::Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename simple_expr::Plus>(_sv.v());
        return ((*(d_a0)).eval_simple() + (*(d_a1)).eval_simple());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename simple_expr::IfPos>(_sv.v());
        if (0u < (*(d_a0)).eval_simple()) {
          return (*(d_a1)).eval_simple();
        } else {
          return (*(d_a2)).eval_simple();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &, simple_expr &, T1 &>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After2 {
        simple_expr *_s0;
        simple_expr _s1;
        simple_expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      /// Intermediate: saves [_result, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After4 {
        T1 _result;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        T1 _result;
        simple_expr _s1;
        simple_expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine5 {
        T1 _result_0;
        T1 _result_1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _After2, _After3, _After4, _Combine1, _Combine5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After3, _After4, _Combine1,
      /// _Combine5.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _After3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(
              _Combine1{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_After4{_result, _f._s1, std::move(_f._s2),
                                      std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine5{_f._result, _result, std::move(_f._s2),
                                        std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._result);
        } else {
          auto _f = std::move(std::get<_Combine5>(_frame));
          _result =
              f1(_f._s4, _result, _f._s3, _f._result_1, _f._s2, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &, simple_expr &, T1 &>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After2 {
        simple_expr *_s0;
        simple_expr _s1;
        simple_expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      /// Intermediate: saves [_result, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After4 {
        T1 _result;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        T1 _result;
        simple_expr _s1;
        simple_expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine5 {
        T1 _result_0;
        T1 _result_1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _After2, _After3, _After4, _Combine1, _Combine5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After3, _After4, _Combine1,
      /// _Combine5.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _After3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(
              _Combine1{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_After4{_result, _f._s1, std::move(_f._s2),
                                      std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine5{_f._result, _result, std::move(_f._s2),
                                        std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._result);
        } else {
          auto _f = std::move(std::get<_Combine5>(_frame));
          _result =
              f1(_f._s4, _result, _f._s3, _f._result_1, _f._s2, _f._result_0);
        }
      }
      return _result;
    }
  };

  /// Shape type demonstrating or-pattern matching.
  struct shape {
    // TYPES
    struct Circle {
      unsigned int d_a0;
    };

    struct Square {
      unsigned int d_a0;
    };

    struct Triangle {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

    shape(const shape &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    shape(shape &&_other) : d_v_(std::move(_other.d_v_)) {}

    shape &operator=(const shape &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    shape &operator=(shape &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    shape clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<Circle>(_sv.v());
        return shape(Circle{d_a0});
      } else if (std::holds_alternative<Square>(_sv.v())) {
        const auto &[d_a0] = std::get<Square>(_sv.v());
        return shape(Square{d_a0});
      } else {
        const auto &[d_a0] = std::get<Triangle>(_sv.v());
        return shape(Triangle{d_a0});
      }
    }

    // CREATORS
    static shape circle(unsigned int a0) {
      return shape(Circle{std::move(a0)});
    }

    static shape square(unsigned int a0) {
      return shape(Square{std::move(a0)});
    }

    static shape triangle(unsigned int a0) {
      return shape(Triangle{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F2 &, unsigned int &>
    T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename shape::Square>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Square>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename shape::Triangle>(_sv.v());
        return f1(d_a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F2 &, unsigned int &>
    T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename shape::Square>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Square>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename shape::Triangle>(_sv.v());
        return f1(d_a0);
      }
    }
  };

  /// sum_shapes l sums values from shapes using unified pattern.
  /// Tests or-pattern style matching in Coq.
  static unsigned int sum_shapes(const List<shape> &l);
  /// count_by_shape l counts shapes: (circles, squares, triangles).
  static std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
  count_by_shape(const List<shape> &l);

  /// Alternative expression type with conditionals for testing different
  /// evaluation patterns.
  struct cond_expr {
    // TYPES
    struct CLit {
      unsigned int d_a0;
    };

    struct CPlus {
      std::unique_ptr<cond_expr> d_a0;
      std::unique_ptr<cond_expr> d_a1;
    };

    struct CCond {
      std::unique_ptr<cond_expr> d_a0;
      std::unique_ptr<cond_expr> d_a1;
      std::unique_ptr<cond_expr> d_a2;
    };

    using variant_t = std::variant<CLit, CPlus, CCond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(CLit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CPlus _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CCond _v) : d_v_(std::move(_v)) {}

    cond_expr(const cond_expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    cond_expr(cond_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    cond_expr &operator=(const cond_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    cond_expr &operator=(cond_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    cond_expr clone() const {
      cond_expr _out{};

      struct _CloneFrame {
        const cond_expr *_src;
        cond_expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const cond_expr *_src = _frame._src;
        cond_expr *_dst = _frame._dst;
        if (std::holds_alternative<CLit>(_src->v())) {
          const auto &_alt = std::get<CLit>(_src->v());
          _dst->d_v_ = CLit{_alt.d_a0};
        } else if (std::holds_alternative<CPlus>(_src->v())) {
          const auto &_alt = std::get<CPlus>(_src->v());
          _dst->d_v_ =
              CPlus{_alt.d_a0 ? std::make_unique<cond_expr>() : nullptr,
                    _alt.d_a1 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<CPlus>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<CCond>(_src->v());
          _dst->d_v_ =
              CCond{_alt.d_a0 ? std::make_unique<cond_expr>() : nullptr,
                    _alt.d_a1 ? std::make_unique<cond_expr>() : nullptr,
                    _alt.d_a2 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<CCond>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static cond_expr clit(unsigned int a0) {
      return cond_expr(CLit{std::move(a0)});
    }

    static cond_expr cplus(cond_expr a0, cond_expr a1) {
      return cond_expr(CPlus{std::make_unique<cond_expr>(std::move(a0)),
                             std::make_unique<cond_expr>(std::move(a1))});
    }

    static cond_expr ccond(cond_expr a0, cond_expr a1, cond_expr a2) {
      return cond_expr(CCond{std::make_unique<cond_expr>(std::move(a0)),
                             std::make_unique<cond_expr>(std::move(a1)),
                             std::make_unique<cond_expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~cond_expr() {
      std::vector<std::unique_ptr<cond_expr>> _stack{};
      auto _drain = [&](cond_expr &_node) {
        if (std::holds_alternative<CPlus>(_node.d_v_)) {
          auto &_alt = std::get<CPlus>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<CCond>(_node.d_v_)) {
          auto &_alt = std::get<CCond>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    /// depth_cond e computes depth of conditional expression tree.
    unsigned int depth_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      /// Intermediate: saves [_s0], dispatches next recursive call.
      struct _After2 {
        cond_expr *_s0;
      };

      /// Intermediate: saves [_s0, _s1], dispatches next recursive call.
      struct _After3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
      };

      /// Intermediate: saves [_result, _s1], dispatches next recursive call.
      struct _After4 {
        unsigned int _result;
        const cond_expr *_s1;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        unsigned int _result;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine5 {
        unsigned int _result_0;
        unsigned int _result_1;
      };

      using _Frame =
          std::variant<_Enter, _After2, _After3, _After4, _Combine1, _Combine5>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After3, _After4, _Combine1,
      /// _Combine5.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_After3{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(_Combine1{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_After4{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine5{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        } else {
          auto _f = std::move(std::get<_Combine5>(_frame));
          _result =
              (std::max(_result, std::max(_f._result_1, _f._result_0)) + 1);
        }
      }
      return _result;
    }

    /// eval_cond e evaluates conditional expression.
    unsigned int eval_cond() const {
      const cond_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename cond_expr::CLit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename cond_expr::CPlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename cond_expr::CPlus>(_sv.v());
        return ((*(d_a0)).eval_cond() + (*(d_a1)).eval_cond());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename cond_expr::CCond>(_sv.v());
        if (0u < (*(d_a0)).eval_cond()) {
          return (*(d_a1)).eval_cond();
        } else {
          return (*(d_a2)).eval_cond();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After2 {
        cond_expr *_s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      /// Intermediate: saves [_result, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After4 {
        T1 _result;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        T1 _result;
        cond_expr _s1;
        cond_expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine5 {
        T1 _result_0;
        T1 _result_1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _After2, _After3, _After4, _Combine1, _Combine5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After3, _After4, _Combine1,
      /// _Combine5.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _After3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(
              _Combine1{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_After4{_result, _f._s1, std::move(_f._s2),
                                      std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine5{_f._result, _result, std::move(_f._s2),
                                        std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._result);
        } else {
          auto _f = std::move(std::get<_Combine5>(_frame));
          _result =
              f1(_f._s4, _result, _f._s3, _f._result_1, _f._s2, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      /// Intermediate: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After2 {
        cond_expr *_s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      /// Intermediate: saves [_s0, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      /// Intermediate: saves [_result, _s1, _s2, _s3, _s4], dispatches next
      /// recursive call.
      struct _After4 {
        T1 _result;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine1 {
        T1 _result;
        cond_expr _s1;
        cond_expr _s2;
      };

      /// Combiner: receives first result, combines with second recursive call.
      struct _Combine5 {
        T1 _result_0;
        T1 _result_1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _After2, _After3, _After4, _Combine1, _Combine5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Frame dispatch: _Enter, _After2, _After3, _After4, _Combine1,
      /// _Combine5.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_After2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _After3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(
              _Combine1{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After3>(_frame)) {
          auto _f = std::move(std::get<_After3>(_frame));
          _stack.emplace_back(_After4{_result, _f._s1, std::move(_f._s2),
                                      std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After4>(_frame)) {
          auto _f = std::move(std::get<_After4>(_frame));
          _stack.emplace_back(_Combine5{_f._result, _result, std::move(_f._s2),
                                        std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine1>(_frame)) {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._result);
        } else {
          auto _f = std::move(std::get<_Combine5>(_frame));
          _result =
              f1(_f._s4, _result, _f._s3, _f._result_1, _f._s2, _f._result_0);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
