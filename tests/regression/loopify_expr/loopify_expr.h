#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

struct LoopifyExpr {
  /// Simple expression ADT with multiple recursive constructors.
  struct expr {
    // TYPES
    struct Val {
      uint64_t a0;
    };

    struct Succ {
      std::unique_ptr<expr> a0;
    };

    struct Add {
      std::unique_ptr<expr> a0;
      std::unique_ptr<expr> a1;
    };

    struct Mul {
      std::unique_ptr<expr> a0;
      std::unique_ptr<expr> a1;
    };

    struct Cond {
      std::unique_ptr<expr> a0;
      std::unique_ptr<expr> a1;
      std::unique_ptr<expr> a2;
    };

    using variant_t = std::variant<Val, Succ, Add, Mul, Cond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Val _v) : v_(std::move(_v)) {}

    explicit expr(Succ _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    explicit expr(Cond _v) : v_(std::move(_v)) {}

    expr(const expr &_other) : v_(std::move(_other.clone().v_)) {}

    expr(expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    expr &operator=(const expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    expr &operator=(expr &&_other) noexcept {
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
        } else if (std::holds_alternative<Succ>(_src->v())) {
          const auto &_alt = std::get<Succ>(_src->v());
          _dst->v_ = Succ{_alt.a0 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Succ>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
        } else if (std::holds_alternative<Add>(_src->v())) {
          const auto &_alt = std::get<Add>(_src->v());
          _dst->v_ = Add{_alt.a0 ? std::make_unique<expr>() : nullptr,
                         _alt.a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Add>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<Mul>(_src->v())) {
          const auto &_alt = std::get<Mul>(_src->v());
          _dst->v_ = Mul{_alt.a0 ? std::make_unique<expr>() : nullptr,
                         _alt.a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Mul>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<Cond>(_src->v());
          _dst->v_ = Cond{_alt.a0 ? std::make_unique<expr>() : nullptr,
                          _alt.a1 ? std::make_unique<expr>() : nullptr,
                          _alt.a2 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Cond>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static expr val(uint64_t a0) { return expr(Val{a0}); }

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
      _stack.reserve(8);
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<Succ>(_node.v_)) {
          auto &_alt = std::get<Succ>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
        }
        if (std::holds_alternative<Add>(_node.v_)) {
          auto &_alt = std::get<Add>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<Mul>(_node.v_)) {
          auto &_alt = std::get<Mul>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<Cond>(_node.v_)) {
          auto &_alt = std::get<Cond>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    expr simplify() const {
      const expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename expr::Val>(_sv.v())) {
        const auto &[a0] = std::get<typename expr::Val>(_sv.v());
        return expr::val(a0);
      } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
        const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
        return expr::succ(a0->simplify());
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
        auto &&_sv0 = a0->simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Val>(_sv0.v());
          if (a00 <= 0) {
            return a1->simplify();
          } else {
            uint64_t n0 = a00 - 1;
            expr s1 = expr::val((n0 + 1));
            auto &&_sv1 = a1->simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
              if (a01 <= 0) {
                return s1;
              } else {
                uint64_t n2 = a01 - 1;
                return expr::add(std::move(s1), expr::val((n2 + 1)));
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
              return expr::add(std::move(s1), expr::succ(*a01));
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
              return expr::add(std::move(s1), expr::add(*a01, *a11));
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
              return expr::add(std::move(s1), expr::mul(*a01, *a11));
            } else {
              const auto &[a01, a11, a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*a00);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else {
          const auto &[a00, a10, a20] = std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*a00, *a10, *a20);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        }
      } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
        auto &&_sv0 = a0->simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Val>(_sv0.v());
          if (a00 <= 0) {
            return expr::val(UINT64_C(0));
          } else {
            uint64_t _x = a00 - 1;
            auto &&_sv1 = a1->simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
              if (a01 <= 0) {
                return expr::val(UINT64_C(0));
              } else {
                uint64_t n1 = a01 - 1;
                expr s2 = expr::val((n1 + 1));
                if (a00 == UINT64_C(1)) {
                  return s2;
                } else {
                  return expr::mul(expr::val(a00), std::move(s2));
                }
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
              expr s2 = expr::succ(*a01);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
              expr s2 = expr::add(*a01, *a11);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
              expr s2 = expr::mul(*a01, *a11);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            } else {
              const auto &[a01, a11, a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              expr s2 = expr::cond(*a01, *a11, *a21);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*a00);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else {
          const auto &[a00, a10, a20] = std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*a00, *a10, *a20);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
        return expr::cond(a0->simplify(), a1->simplify(), a2->simplify());
      }
    }

    /// size e counts total number of nodes.
    uint64_t size() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
      };

      /// _After_Cond: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Cond {
        const expr *_s0;
        const expr *_s1;
      };

      /// _After_Cond_1: saves [_result, _s1], dispatches next recursive call.
      struct _After_Cond_1 {
        uint64_t _result;
        const expr *_s1;
      };

      /// _After_Mul: saves [_s0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        uint64_t _result;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        uint64_t _result_0;
        uint64_t _result_1;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        uint64_t _result;
      };

      /// _Resume_Succ: resumes after recursive call with _result.
      struct _Resume_Succ {};

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _After_Mul, _Combine_Add,
                                  _Combine_Cond, _Combine_Mul, _Resume_Succ>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified size: _Enter -> _After_Add -> _After_Cond -> _After_Cond_1
      /// -> _After_Mul -> _Combine_Add -> _Combine_Cond -> _Combine_Mul ->
      /// _Resume_Succ.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume_Succ{});
            _stack.emplace_back(_Enter{a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(_Combine_Mul{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = ((_result + _f._result) + 1);
        } else if (std::holds_alternative<_Combine_Cond>(_frame)) {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result = ((_result + (_f._result_1 + _f._result_0)) + 1);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = ((_result + _f._result) + 1);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = (_result + 1);
        }
      }
      return _result;
    }

    /// count_vals e counts the number of Val nodes.
    uint64_t count_vals() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
      };

      /// _After_Cond: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Cond {
        const expr *_s0;
        const expr *_s1;
      };

      /// _After_Cond_1: saves [_result, _s1], dispatches next recursive call.
      struct _After_Cond_1 {
        uint64_t _result;
        const expr *_s1;
      };

      /// _After_Mul: saves [_s0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        uint64_t _result;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        uint64_t _result_0;
        uint64_t _result_1;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        uint64_t _result;
      };

      using _Frame =
          std::variant<_Enter, _After_Add, _After_Cond, _After_Cond_1,
                       _After_Mul, _Combine_Add, _Combine_Cond, _Combine_Mul>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified count_vals: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _After_Mul -> _Combine_Add -> _Combine_Cond ->
      /// _Combine_Mul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Enter{a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(_Combine_Mul{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = (_result + _f._result);
        } else if (std::holds_alternative<_Combine_Cond>(_frame)) {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result = (_result + (_f._result_1 + _f._result_0));
        } else {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = (_result + _f._result);
        }
      }
      return _result;
    }

    /// depth e computes expression depth.
    uint64_t depth() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
      };

      /// _After_Cond: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Cond {
        const expr *_s0;
        const expr *_s1;
      };

      /// _After_Cond_1: saves [_result, _s1], dispatches next recursive call.
      struct _After_Cond_1 {
        uint64_t _result;
        const expr *_s1;
      };

      /// _After_Mul: saves [_s0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        uint64_t _result;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        uint64_t _result_0;
        uint64_t _result_1;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        uint64_t _result;
      };

      /// _Resume_Succ: resumes after recursive call with _result.
      struct _Resume_Succ {};

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _After_Mul, _Combine_Add,
                                  _Combine_Cond, _Combine_Mul, _Resume_Succ>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified depth: _Enter -> _After_Add -> _After_Cond -> _After_Cond_1
      /// -> _After_Mul -> _Combine_Add -> _Combine_Cond -> _Combine_Mul ->
      /// _Resume_Succ.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume_Succ{});
            _stack.emplace_back(_Enter{a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(_Combine_Mul{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        } else if (std::holds_alternative<_Combine_Cond>(_frame)) {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result =
              (std::max(_result, std::max(_f._result_1, _f._result_0)) + 1);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = (_result + 1);
        }
      }
      return _result;
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    uint64_t eval() const {
      const expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename expr::Val>(_sv.v())) {
        const auto &[a0] = std::get<typename expr::Val>(_sv.v());
        return a0;
      } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
        const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
        return (a0->eval() + 1);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
        return (a0->eval() + a1->eval());
      } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
        return (a0->eval() * a1->eval());
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
        if (UINT64_C(0) < a0->eval()) {
          return a1->eval();
        } else {
          return a2->eval();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, expr &, T1 &, expr &, T1 &,
                                     expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
        expr a1;
        expr a0;
      };

      /// _After_Cond: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_Cond {
        const expr *_s0;
        const expr *_s1;
        expr a2;
        expr a1;
        expr a0;
      };

      /// _After_Cond_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Cond_1 {
        T1 _result;
        const expr *_s1;
        expr a2;
        expr a1;
        expr a0;
      };

      /// _After_Mul: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
        expr a1;
        expr a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        T1 _result;
        expr a1;
        expr a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        T1 _result_0;
        T1 _result_1;
        expr a2;
        expr a1;
        expr a0;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        T1 _result;
        expr a1;
        expr a0;
      };

      /// _Resume_Succ: saves [f0, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Succ {
        F1 f0;
        expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _After_Mul, _Combine_Add,
                                  _Combine_Cond, _Combine_Mul, _Resume_Succ>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rec: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _After_Mul -> _Combine_Add -> _Combine_Cond ->
      /// _Combine_Mul -> _Resume_Succ.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume_Succ{f0, *a0});
            _stack.emplace_back(_Enter{a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(
              _Combine_Add{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1, std::move(_f.a2),
                                            std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result,
                                            std::move(_f.a2), std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(
              _Combine_Mul{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f1(_f.a0, _result, _f.a1, _f._result);
        } else if (std::holds_alternative<_Combine_Cond>(_frame)) {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result =
              f3(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = f2(_f.a0, _result, _f.a1, _f._result);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = _f.f0(_f.a0, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, expr &, T1 &, expr &, T1 &,
                                     expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
        expr a1;
        expr a0;
      };

      /// _After_Cond: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_Cond {
        const expr *_s0;
        const expr *_s1;
        expr a2;
        expr a1;
        expr a0;
      };

      /// _After_Cond_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Cond_1 {
        T1 _result;
        const expr *_s1;
        expr a2;
        expr a1;
        expr a0;
      };

      /// _After_Mul: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
        expr a1;
        expr a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        T1 _result;
        expr a1;
        expr a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        T1 _result_0;
        T1 _result_1;
        expr a2;
        expr a1;
        expr a0;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        T1 _result;
        expr a1;
        expr a0;
      };

      /// _Resume_Succ: saves [f0, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Succ {
        F1 f0;
        expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _After_Mul, _Combine_Add,
                                  _Combine_Cond, _Combine_Mul, _Resume_Succ>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rect: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _After_Mul -> _Combine_Add -> _Combine_Cond ->
      /// _Combine_Mul -> _Resume_Succ.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume_Succ{f0, *a0});
            _stack.emplace_back(_Enter{a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(
              _Combine_Add{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1, std::move(_f.a2),
                                            std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result,
                                            std::move(_f.a2), std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(
              _Combine_Mul{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f1(_f.a0, _result, _f.a1, _f._result);
        } else if (std::holds_alternative<_Combine_Cond>(_frame)) {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result =
              f3(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = f2(_f.a0, _result, _f.a1, _f._result);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = _f.f0(_f.a0, _result);
        }
      }
      return _result;
    }
  };

  /// Alternative expression type for testing different evaluation strategy.
  struct simple_expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Plus {
      std::unique_ptr<simple_expr> a0;
      std::unique_ptr<simple_expr> a1;
    };

    struct IfPos {
      std::unique_ptr<simple_expr> a0;
      std::unique_ptr<simple_expr> a1;
      std::unique_ptr<simple_expr> a2;
    };

    using variant_t = std::variant<Lit, Plus, IfPos>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    simple_expr() {}

    explicit simple_expr(Lit _v) : v_(std::move(_v)) {}

    explicit simple_expr(Plus _v) : v_(std::move(_v)) {}

    explicit simple_expr(IfPos _v) : v_(std::move(_v)) {}

    simple_expr(const simple_expr &_other) : v_(std::move(_other.clone().v_)) {}

    simple_expr(simple_expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    simple_expr &operator=(const simple_expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    simple_expr &operator=(simple_expr &&_other) noexcept {
      v_ = std::move(_other.v_);
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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const simple_expr *_src = _frame._src;
        simple_expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->v_ = Lit{_alt.a0};
        } else if (std::holds_alternative<Plus>(_src->v())) {
          const auto &_alt = std::get<Plus>(_src->v());
          _dst->v_ = Plus{_alt.a0 ? std::make_unique<simple_expr>() : nullptr,
                          _alt.a1 ? std::make_unique<simple_expr>() : nullptr};
          auto &_dst_alt = std::get<Plus>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<IfPos>(_src->v());
          _dst->v_ = IfPos{_alt.a0 ? std::make_unique<simple_expr>() : nullptr,
                           _alt.a1 ? std::make_unique<simple_expr>() : nullptr,
                           _alt.a2 ? std::make_unique<simple_expr>() : nullptr};
          auto &_dst_alt = std::get<IfPos>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static simple_expr lit(uint64_t a0) { return simple_expr(Lit{a0}); }

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
      _stack.reserve(8);
      auto _drain = [&](simple_expr &_node) {
        if (std::holds_alternative<Plus>(_node.v_)) {
          auto &_alt = std::get<Plus>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<IfPos>(_node.v_)) {
          auto &_alt = std::get<IfPos>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

    /// depth_simple e computes depth of simple expression tree.
    uint64_t depth_simple() const {
      const simple_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_expr *_self;
      };

      /// _After_IfPos: saves [_s0, _s1], dispatches next recursive call.
      struct _After_IfPos {
        const simple_expr *_s0;
        const simple_expr *_s1;
      };

      /// _After_IfPos_1: saves [_result, _s1], dispatches next recursive call.
      struct _After_IfPos_1 {
        uint64_t _result;
        const simple_expr *_s1;
      };

      /// _After_Plus: saves [_s0], dispatches next recursive call.
      struct _After_Plus {
        simple_expr *_s0;
      };

      /// _Combine_IfPos: receives partial results, combines with _result from
      /// final call.
      struct _Combine_IfPos {
        uint64_t _result_0;
        uint64_t _result_1;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_IfPos, _After_IfPos_1,
                                  _After_Plus, _Combine_IfPos, _Combine_Plus>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified depth_simple: _Enter -> _After_IfPos -> _After_IfPos_1 ->
      /// _After_Plus -> _Combine_IfPos -> _Combine_Plus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_After_IfPos{a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_IfPos>(_frame)) {
          auto _f = std::move(std::get<_After_IfPos>(_frame));
          _stack.emplace_back(_After_IfPos_1{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<_After_IfPos_1>(_frame));
          _stack.emplace_back(_Combine_IfPos{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(_Combine_Plus{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Combine_IfPos>(_frame));
          _result =
              (std::max(_result, std::max(_f._result_1, _f._result_0)) + 1);
        } else {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        }
      }
      return _result;
    }

    /// eval_simple e evaluates simple expression with positive test.
    uint64_t eval_simple() const {
      const simple_expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
        const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
        return a0;
      } else if (std::holds_alternative<typename simple_expr::Plus>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename simple_expr::Plus>(_sv.v());
        return (a0->eval_simple() + a1->eval_simple());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename simple_expr::IfPos>(_sv.v());
        if (UINT64_C(0) < a0->eval_simple()) {
          return a1->eval_simple();
        } else {
          return a2->eval_simple();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &, simple_expr &, T1 &>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_expr *_self;
      };

      /// _After_IfPos: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_IfPos {
        const simple_expr *_s0;
        const simple_expr *_s1;
        simple_expr a2;
        simple_expr a1;
        simple_expr a0;
      };

      /// _After_IfPos_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_IfPos_1 {
        T1 _result;
        const simple_expr *_s1;
        simple_expr a2;
        simple_expr a1;
        simple_expr a0;
      };

      /// _After_Plus: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Plus {
        simple_expr *_s0;
        simple_expr a1;
        simple_expr a0;
      };

      /// _Combine_IfPos: receives partial results, combines with _result from
      /// final call.
      struct _Combine_IfPos {
        T1 _result_0;
        T1 _result_1;
        simple_expr a2;
        simple_expr a1;
        simple_expr a0;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        T1 _result;
        simple_expr a1;
        simple_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_IfPos, _After_IfPos_1,
                                  _After_Plus, _Combine_IfPos, _Combine_Plus>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_expr_rec: _Enter -> _After_IfPos -> _After_IfPos_1 ->
      /// _After_Plus -> _Combine_IfPos -> _Combine_Plus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _After_IfPos{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_IfPos>(_frame)) {
          auto _f = std::move(std::get<_After_IfPos>(_frame));
          _stack.emplace_back(_After_IfPos_1{_result, _f._s1, std::move(_f.a2),
                                             std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<_After_IfPos_1>(_frame));
          _stack.emplace_back(_Combine_IfPos{_f._result, _result,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(
              _Combine_Plus{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Combine_IfPos>(_frame));
          _result =
              f1(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        } else {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &, simple_expr &, T1 &>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_expr *_self;
      };

      /// _After_IfPos: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_IfPos {
        const simple_expr *_s0;
        const simple_expr *_s1;
        simple_expr a2;
        simple_expr a1;
        simple_expr a0;
      };

      /// _After_IfPos_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_IfPos_1 {
        T1 _result;
        const simple_expr *_s1;
        simple_expr a2;
        simple_expr a1;
        simple_expr a0;
      };

      /// _After_Plus: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Plus {
        simple_expr *_s0;
        simple_expr a1;
        simple_expr a0;
      };

      /// _Combine_IfPos: receives partial results, combines with _result from
      /// final call.
      struct _Combine_IfPos {
        T1 _result_0;
        T1 _result_1;
        simple_expr a2;
        simple_expr a1;
        simple_expr a0;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        T1 _result;
        simple_expr a1;
        simple_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_IfPos, _After_IfPos_1,
                                  _After_Plus, _Combine_IfPos, _Combine_Plus>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_expr_rect: _Enter -> _After_IfPos -> _After_IfPos_1
      /// -> _After_Plus -> _Combine_IfPos -> _Combine_Plus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _After_IfPos{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_IfPos>(_frame)) {
          auto _f = std::move(std::get<_After_IfPos>(_frame));
          _stack.emplace_back(_After_IfPos_1{_result, _f._s1, std::move(_f.a2),
                                             std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<_After_IfPos_1>(_frame));
          _stack.emplace_back(_Combine_IfPos{_f._result, _result,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(
              _Combine_Plus{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Combine_IfPos>(_frame));
          _result =
              f1(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        } else {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }
  };

  /// Shape type demonstrating or-pattern matching.
  struct shape {
    // TYPES
    struct Circle {
      uint64_t a0;
    };

    struct Square {
      uint64_t a0;
    };

    struct Triangle {
      uint64_t a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : v_(std::move(_v)) {}

    explicit shape(Square _v) : v_(std::move(_v)) {}

    explicit shape(Triangle _v) : v_(std::move(_v)) {}

    shape(const shape &_other) : v_(std::move(_other.clone().v_)) {}

    shape(shape &&_other) noexcept : v_(std::move(_other.v_)) {}

    shape &operator=(const shape &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    shape &operator=(shape &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    shape clone() const {
      if (std::holds_alternative<Circle>(this->v())) {
        const auto &[a0] = std::get<Circle>(this->v());
        return shape(Circle{a0});
      } else if (std::holds_alternative<Square>(this->v())) {
        const auto &[a0] = std::get<Square>(this->v());
        return shape(Square{a0});
      } else {
        const auto &[a0] = std::get<Triangle>(this->v());
        return shape(Triangle{a0});
      }
    }

    // CREATORS
    static shape circle(uint64_t a0) { return shape(Circle{a0}); }

    static shape square(uint64_t a0) { return shape(Square{a0}); }

    static shape triangle(uint64_t a0) { return shape(Triangle{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename shape::Square>(this->v())) {
        const auto &[a0] = std::get<typename shape::Square>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename shape::Triangle>(this->v());
        return f1(a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename shape::Square>(this->v())) {
        const auto &[a0] = std::get<typename shape::Square>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename shape::Triangle>(this->v());
        return f1(a0);
      }
    }
  };

  /// sum_shapes l sums values from shapes using unified pattern.
  /// Tests or-pattern style matching in Coq.
  static uint64_t sum_shapes(const List<shape> &l);
  /// count_by_shape l counts shapes: (circles, squares, triangles).
  static std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
  count_by_shape(const List<shape> &l);

  /// Alternative expression type with conditionals for testing different
  /// evaluation patterns.
  struct cond_expr {
    // TYPES
    struct CLit {
      uint64_t a0;
    };

    struct CPlus {
      std::unique_ptr<cond_expr> a0;
      std::unique_ptr<cond_expr> a1;
    };

    struct CCond {
      std::unique_ptr<cond_expr> a0;
      std::unique_ptr<cond_expr> a1;
      std::unique_ptr<cond_expr> a2;
    };

    using variant_t = std::variant<CLit, CPlus, CCond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(CLit _v) : v_(std::move(_v)) {}

    explicit cond_expr(CPlus _v) : v_(std::move(_v)) {}

    explicit cond_expr(CCond _v) : v_(std::move(_v)) {}

    cond_expr(const cond_expr &_other) : v_(std::move(_other.clone().v_)) {}

    cond_expr(cond_expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    cond_expr &operator=(const cond_expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    cond_expr &operator=(cond_expr &&_other) noexcept {
      v_ = std::move(_other.v_);
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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const cond_expr *_src = _frame._src;
        cond_expr *_dst = _frame._dst;
        if (std::holds_alternative<CLit>(_src->v())) {
          const auto &_alt = std::get<CLit>(_src->v());
          _dst->v_ = CLit{_alt.a0};
        } else if (std::holds_alternative<CPlus>(_src->v())) {
          const auto &_alt = std::get<CPlus>(_src->v());
          _dst->v_ = CPlus{_alt.a0 ? std::make_unique<cond_expr>() : nullptr,
                           _alt.a1 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<CPlus>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<CCond>(_src->v());
          _dst->v_ = CCond{_alt.a0 ? std::make_unique<cond_expr>() : nullptr,
                           _alt.a1 ? std::make_unique<cond_expr>() : nullptr,
                           _alt.a2 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<CCond>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static cond_expr clit(uint64_t a0) { return cond_expr(CLit{a0}); }

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
      _stack.reserve(8);
      auto _drain = [&](cond_expr &_node) {
        if (std::holds_alternative<CPlus>(_node.v_)) {
          auto &_alt = std::get<CPlus>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<CCond>(_node.v_)) {
          auto &_alt = std::get<CCond>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

    /// depth_cond e computes depth of conditional expression tree.
    uint64_t depth_cond() const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_CCond: saves [_s0, _s1], dispatches next recursive call.
      struct _After_CCond {
        const cond_expr *_s0;
        const cond_expr *_s1;
      };

      /// _After_CCond_1: saves [_result, _s1], dispatches next recursive call.
      struct _After_CCond_1 {
        uint64_t _result;
        const cond_expr *_s1;
      };

      /// _After_CPlus: saves [_s0], dispatches next recursive call.
      struct _After_CPlus {
        cond_expr *_s0;
      };

      /// _Combine_CCond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_CCond {
        uint64_t _result_0;
        uint64_t _result_1;
      };

      /// _Combine_CPlus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_CPlus {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_CCond, _After_CCond_1,
                                  _After_CPlus, _Combine_CCond, _Combine_CPlus>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified depth_cond: _Enter -> _After_CCond -> _After_CCond_1 ->
      /// _After_CPlus -> _Combine_CCond -> _Combine_CPlus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_After_CPlus{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_After_CCond{a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_CCond>(_frame)) {
          auto _f = std::move(std::get<_After_CCond>(_frame));
          _stack.emplace_back(_After_CCond_1{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_CCond_1>(_frame)) {
          auto _f = std::move(std::get<_After_CCond_1>(_frame));
          _stack.emplace_back(_Combine_CCond{_f._result, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_CPlus>(_frame)) {
          auto _f = std::move(std::get<_After_CPlus>(_frame));
          _stack.emplace_back(_Combine_CPlus{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_CCond>(_frame)) {
          auto _f = std::move(std::get<_Combine_CCond>(_frame));
          _result =
              (std::max(_result, std::max(_f._result_1, _f._result_0)) + 1);
        } else {
          auto _f = std::move(std::get<_Combine_CPlus>(_frame));
          _result = (std::max(_result, _f._result) + 1);
        }
      }
      return _result;
    }

    /// eval_cond e evaluates conditional expression.
    uint64_t eval_cond() const {
      const cond_expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
        const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
        return a0;
      } else if (std::holds_alternative<typename cond_expr::CPlus>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
        return (a0->eval_cond() + a1->eval_cond());
      } else {
        const auto &[a0, a1, a2] = std::get<typename cond_expr::CCond>(_sv.v());
        if (UINT64_C(0) < a0->eval_cond()) {
          return a1->eval_cond();
        } else {
          return a2->eval_cond();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_CCond: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_CCond {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_CCond_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_CCond_1 {
        T1 _result;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_CPlus: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_CPlus {
        cond_expr *_s0;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_CCond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_CCond {
        T1 _result_0;
        T1 _result_1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_CPlus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_CPlus {
        T1 _result;
        cond_expr a1;
        cond_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_CCond, _After_CCond_1,
                                  _After_CPlus, _Combine_CCond, _Combine_CPlus>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rec: _Enter -> _After_CCond -> _After_CCond_1 ->
      /// _After_CPlus -> _Combine_CCond -> _Combine_CPlus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_After_CPlus{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _After_CCond{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_CCond>(_frame)) {
          auto _f = std::move(std::get<_After_CCond>(_frame));
          _stack.emplace_back(_After_CCond_1{_result, _f._s1, std::move(_f.a2),
                                             std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_CCond_1>(_frame)) {
          auto _f = std::move(std::get<_After_CCond_1>(_frame));
          _stack.emplace_back(_Combine_CCond{_f._result, _result,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_CPlus>(_frame)) {
          auto _f = std::move(std::get<_After_CPlus>(_frame));
          _stack.emplace_back(
              _Combine_CPlus{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_CCond>(_frame)) {
          auto _f = std::move(std::get<_Combine_CCond>(_frame));
          _result =
              f1(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        } else {
          auto _f = std::move(std::get<_Combine_CPlus>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_CCond: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_CCond {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_CCond_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_CCond_1 {
        T1 _result;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_CPlus: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_CPlus {
        cond_expr *_s0;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_CCond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_CCond {
        T1 _result_0;
        T1 _result_1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_CPlus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_CPlus {
        T1 _result;
        cond_expr a1;
        cond_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_CCond, _After_CCond_1,
                                  _After_CPlus, _Combine_CCond, _Combine_CPlus>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rect: _Enter -> _After_CCond -> _After_CCond_1 ->
      /// _After_CPlus -> _Combine_CCond -> _Combine_CPlus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_After_CPlus{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _After_CCond{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_CCond>(_frame)) {
          auto _f = std::move(std::get<_After_CCond>(_frame));
          _stack.emplace_back(_After_CCond_1{_result, _f._s1, std::move(_f.a2),
                                             std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_CCond_1>(_frame)) {
          auto _f = std::move(std::get<_After_CCond_1>(_frame));
          _stack.emplace_back(_Combine_CCond{_f._result, _result,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_CPlus>(_frame)) {
          auto _f = std::move(std::get<_After_CPlus>(_frame));
          _stack.emplace_back(
              _Combine_CPlus{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_CCond>(_frame)) {
          auto _f = std::move(std::get<_Combine_CCond>(_frame));
          _result =
              f1(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        } else {
          auto _f = std::move(std::get<_Combine_CPlus>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
