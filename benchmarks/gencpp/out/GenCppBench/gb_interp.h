#ifndef INCLUDED_GB_INTERP
#define INCLUDED_GB_INTERP

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  List<A> tl() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[_, a1] = std::get<typename List<A>::Cons>(this->v());
      return *a1;
    }
  }

  A hd(A default0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return default0;
    } else {
      const auto &[a0, _] = std::get<typename List<A>::Cons>(this->v());
      return a0;
    }
  }
};

struct GbInterp {
  static uint64_t next(uint64_t s);
  static List<uint64_t> randoms(uint64_t n, uint64_t s);

  struct expr {
    // TYPES
    struct Num {
      uint64_t n;
    };

    struct Var {
      uint64_t i;
    };

    struct Add {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> b;
    };

    struct Mul {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> b;
    };

    struct Let {
      std::shared_ptr<expr> e;
      std::shared_ptr<expr> body;
    };

    struct If0 {
      std::shared_ptr<expr> c;
      std::shared_ptr<expr> t;
      std::shared_ptr<expr> e;
    };

    using variant_t = std::variant<Num, Var, Add, Mul, Let, If0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Num _v) : v_(std::move(_v)) {}

    explicit expr(Var _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    explicit expr(Let _v) : v_(std::move(_v)) {}

    explicit expr(If0 _v) : v_(std::move(_v)) {}

    static expr num(uint64_t n) { return expr(Num{n}); }

    static expr var(uint64_t i) { return expr(Var{i}); }

    static expr add(crane::shared_child_slot<expr> a,
                    crane::shared_child_slot<expr> b) {
      return expr(Add{a.take(), b.take()});
    }

    static expr mul(crane::shared_child_slot<expr> a,
                    crane::shared_child_slot<expr> b) {
      return expr(Mul{a.take(), b.take()});
    }

    static expr let(crane::shared_child_slot<expr> e,
                    crane::shared_child_slot<expr> body) {
      return expr(Let{e.take(), body.take()});
    }

    static expr if0(crane::shared_child_slot<expr> c,
                    crane::shared_child_slot<expr> t,
                    crane::shared_child_slot<expr> e) {
      return expr(If0{c.take(), t.take(), e.take()});
    }

    // MANIPULATORS
    ~expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Num>(v_mut())) {
        return;
      }
      if (std::holds_alternative<Var>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Add>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->b && _alt->b.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Mul>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->b && _alt->b.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Let>(&v_mut())) {
        if (!((_alt->e && _alt->e.use_count() == 1) ||
              (_alt->body && _alt->body.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<If0>(&v_mut())) {
        if (!((_alt->c && _alt->c.use_count() == 1) ||
              (_alt->t && _alt->t.use_count() == 1) ||
              (_alt->e && _alt->e.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->b && _alt->b.use_count() == 1) {
            _stack.push_back(std::move(_alt->b));
          }
        }
        if (auto *_alt = std::get_if<Mul>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->b && _alt->b.use_count() == 1) {
            _stack.push_back(std::move(_alt->b));
          }
        }
        if (auto *_alt = std::get_if<Let>(&_v)) {
          if (_alt->e && _alt->e.use_count() == 1) {
            _stack.push_back(std::move(_alt->e));
          }
          if (_alt->body && _alt->body.use_count() == 1) {
            _stack.push_back(std::move(_alt->body));
          }
        }
        if (auto *_alt = std::get_if<If0>(&_v)) {
          if (_alt->c && _alt->c.use_count() == 1) {
            _stack.push_back(std::move(_alt->c));
          }
          if (_alt->t && _alt->t.use_count() == 1) {
            _stack.push_back(std::move(_alt->t));
          }
          if (_alt->e && _alt->e.use_count() == 1) {
            _stack.push_back(std::move(_alt->e));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    expr simplify() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of simplify: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_simplify_in_Add {
        const expr *b0;
      };

      struct _after_simplify_in_Add_2 {
        expr _tmp2;
      };

      struct _after_simplify_in_If0 {
        const expr *t0;
        const expr *e0;
      };

      struct _after_simplify_in_If0_2 {
        const expr *e0;
        expr _tmp9;
      };

      struct _after_simplify_in_If0_3 {
        expr _tmp9;
        expr _tmp8;
      };

      struct _after_simplify_in_Let {
        const expr *body0;
      };

      struct _after_simplify_in_Let_2 {
        expr _tmp6;
      };

      struct _after_simplify_in_Mul {
        const expr *b0;
      };

      struct _after_simplify_in_Mul_2 {
        expr _tmp4;
      };

      using _frame =
          std::variant<_call, _after_simplify_in_Add, _after_simplify_in_Add_2,
                       _after_simplify_in_If0, _after_simplify_in_If0_2,
                       _after_simplify_in_If0_3, _after_simplify_in_Let,
                       _after_simplify_in_Let_2, _after_simplify_in_Mul,
                       _after_simplify_in_Mul_2>;
      expr _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, b0] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_simplify_in_Add{crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, b0] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_simplify_in_Mul{crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Let>(_sv.v())) {
            const auto &[e0, body0] = std::get<typename expr::Let>(_sv.v());
            _stack.emplace_back(_after_simplify_in_Let{crane_raw(body0)});
            _stack.emplace_back(_call{crane_raw(e0)});
          } else if (std::holds_alternative<typename expr::If0>(_sv.v())) {
            const auto &[c0, t0, e0] = std::get<typename expr::If0>(_sv.v());
            _stack.emplace_back(
                _after_simplify_in_If0{crane_raw(t0), crane_raw(e0)});
            _stack.emplace_back(_call{crane_raw(c0)});
          } else {
            _result = *_self;
          }
        } else if (std::holds_alternative<_after_simplify_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Add>(_popped));
          _stack.pop_back();
          const expr &b0 = *_f.b0;
          _stack.emplace_back(_after_simplify_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else if (std::holds_alternative<_after_simplify_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Add_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp2.sadd(std::move(_result));
        } else if (std::holds_alternative<_after_simplify_in_If0>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_If0>(_popped));
          _stack.pop_back();
          const expr &t0 = *_f.t0;
          const expr &e0 = *_f.e0;
          _stack.emplace_back(_after_simplify_in_If0_2{&e0,
                                                       std::move(_result)});
          _stack.emplace_back(_call{_f.t0});
        } else if (std::holds_alternative<_after_simplify_in_If0_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_If0_2>(_popped));
          _stack.pop_back();
          const expr &e0 = *_f.e0;
          _stack.emplace_back(
              _after_simplify_in_If0_3{std::move(_f._tmp9),
                                       std::move(_result)});
          _stack.emplace_back(_call{_f.e0});
        } else if (std::holds_alternative<_after_simplify_in_If0_3>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_If0_3>(_popped));
          _stack.pop_back();
          _result = expr::if0(std::move(_f._tmp9), std::move(_f._tmp8),
                              std::move(_result));
        } else if (std::holds_alternative<_after_simplify_in_Let>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Let>(_popped));
          _stack.pop_back();
          const expr &body0 = *_f.body0;
          _stack.emplace_back(_after_simplify_in_Let_2{std::move(_result)});
          _stack.emplace_back(_call{_f.body0});
        } else if (std::holds_alternative<_after_simplify_in_Let_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Let_2>(_popped));
          _stack.pop_back();
          _result = expr::let(std::move(_f._tmp6), std::move(_result));
        } else if (std::holds_alternative<_after_simplify_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Mul>(_popped));
          _stack.pop_back();
          const expr &b0 = *_f.b0;
          _stack.emplace_back(_after_simplify_in_Mul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else {
          auto _f = std::move(std::get<_after_simplify_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp4.smul(std::move(_result));
        }
      }
      return _result;
    }

    expr smul(expr b) const {
      if (this->is_num(UINT64_C(1))) {
        return b;
      } else {
        if (b.is_num(UINT64_C(1))) {
          return *this;
        } else {
          return expr::mul(crane::shared_child(this), std::move(b));
        }
      }
    }

    expr sadd(const expr &b) const {
      if (this->is_num(UINT64_C(0))) {
        return b;
      } else {
        if (b.is_num(UINT64_C(0))) {
          return *this;
        } else {
          if (std::holds_alternative<typename expr::Num>(this->v())) {
            const auto &[n] = std::get<typename expr::Num>(this->v());
            if (std::holds_alternative<typename expr::Num>(b.v())) {
              const auto &[n0] = std::get<typename expr::Num>(b.v());
              auto &&_once1 = (n + n0);
              auto &&_once2 = UINT64_C(4096);
              return expr::num((_once2 ? _once1 % _once2 : _once1));
            } else {
              return expr::add(crane::shared_child(this), b);
            }
          } else {
            return expr::add(crane::shared_child(this), b);
          }
        }
      }
    }

    bool is_num(uint64_t n) const {
      if (std::holds_alternative<typename expr::Num>(this->v())) {
        const auto &[n0] = std::get<typename expr::Num>(this->v());
        return n0 == n;
      } else {
        return false;
      }
    }

    uint64_t eval(const List<uint64_t> &env) const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
        List<uint64_t> env;
      };

      struct _after_eval_in_Add {
        List<uint64_t> env;
        const expr *b0;
      };

      struct _after_eval_in_Add_2 {
        uint64_t _tmp2;
      };

      struct _after_eval_in_If0 {
        List<uint64_t> env;
        const expr *t0;
        const expr *e0;
      };

      struct _after_eval_in_Let {
        List<uint64_t> env;
        const expr *body0;
      };

      struct _after_eval_in_Mul {
        List<uint64_t> env;
        const expr *b0;
      };

      struct _after_eval_in_Mul_2 {
        uint64_t _tmp4;
      };

      using _frame = std::variant<
          _call, _after_eval_in_Add, _after_eval_in_Add_2, _after_eval_in_If0,
          _after_eval_in_Let, _after_eval_in_Mul, _after_eval_in_Mul_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self, env});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          const List<uint64_t> &env = _f.env;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Num>(_sv.v())) {
            const auto &[n0] = std::get<typename expr::Num>(_sv.v());
            _result = std::move(n0);
          } else if (std::holds_alternative<typename expr::Var>(_sv.v())) {
            const auto &[i0] = std::get<typename expr::Var>(_sv.v());
            _result = lookup(env, i0);
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, b0] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_eval_in_Add{env, crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0), env});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, b0] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_eval_in_Mul{env, crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0), env});
          } else if (std::holds_alternative<typename expr::Let>(_sv.v())) {
            const auto &[e0, body0] = std::get<typename expr::Let>(_sv.v());
            _stack.emplace_back(_after_eval_in_Let{env, crane_raw(body0)});
            _stack.emplace_back(_call{crane_raw(e0), env});
          } else {
            const auto &[c0, t0, e0] = std::get<typename expr::If0>(_sv.v());
            _stack.emplace_back(
                _after_eval_in_If0{env, crane_raw(t0), crane_raw(e0)});
            _stack.emplace_back(_call{crane_raw(c0), env});
          }
        } else if (std::holds_alternative<_after_eval_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Add>(_popped));
          _stack.pop_back();
          List<uint64_t> env = std::move(_f.env);
          const expr &b0 = *_f.b0;
          _stack.emplace_back(_after_eval_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.b0, std::move(env)});
        } else if (std::holds_alternative<_after_eval_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Add_2>(_popped));
          _stack.pop_back();
          auto &&_once3 = (_f._tmp2 + std::move(_result));
          auto &&_once4 = UINT64_C(4096);
          _result = (_once4 ? _once3 % _once4 : _once3);
        } else if (std::holds_alternative<_after_eval_in_If0>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_If0>(_popped));
          _stack.pop_back();
          List<uint64_t> env = std::move(_f.env);
          const expr &t0 = *_f.t0;
          const expr &e0 = *_f.e0;
          if (std::move(_result) == UINT64_C(0)) {
            _stack.emplace_back(_call{_f.t0, std::move(env)});
          } else {
            _stack.emplace_back(_call{_f.e0, std::move(env)});
          }
        } else if (std::holds_alternative<_after_eval_in_Let>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Let>(_popped));
          _stack.pop_back();
          List<uint64_t> env = std::move(_f.env);
          const expr &body0 = *_f.body0;
          _stack.emplace_back(
              _call{_f.body0,
                    List<uint64_t>::cons(std::move(_result), std::move(env))});
        } else if (std::holds_alternative<_after_eval_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Mul>(_popped));
          _stack.pop_back();
          List<uint64_t> env = std::move(_f.env);
          const expr &b0 = *_f.b0;
          _stack.emplace_back(_after_eval_in_Mul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.b0, std::move(env)});
        } else {
          auto _f = std::move(std::get<_after_eval_in_Mul_2>(_popped));
          _stack.pop_back();
          auto &&_once5 = (_f._tmp4 * std::move(_result));
          auto &&_once6 = UINT64_C(4096);
          _result = (_once6 ? _once5 % _once6 : _once5);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F5>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4) const {
      return this->template expr_rect<T1>(f, f0, f1, f2, f3, f4);
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F5>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const uint64_t &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4) const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_expr_rect_in_Add {
        std::shared_ptr<expr> a0;
        const expr *b0;
      };

      struct _after_expr_rect_in_Add_2 {
        std::shared_ptr<expr> a0;
        const expr *b0;
        T1 _tmp2;
      };

      struct _after_expr_rect_in_If0 {
        std::shared_ptr<expr> c0;
        const expr *t0;
        const expr *e1;
      };

      struct _after_expr_rect_in_If0_2 {
        std::shared_ptr<expr> c0;
        const expr *t0;
        const expr *e1;
        T1 _tmp9;
      };

      struct _after_expr_rect_in_If0_3 {
        std::shared_ptr<expr> c0;
        const expr *t0;
        const expr *e1;
        T1 _tmp9;
        T1 _tmp8;
      };

      struct _after_expr_rect_in_Let {
        std::shared_ptr<expr> e1;
        const expr *body0;
      };

      struct _after_expr_rect_in_Let_2 {
        std::shared_ptr<expr> e1;
        const expr *body0;
        T1 _tmp6;
      };

      struct _after_expr_rect_in_Mul {
        std::shared_ptr<expr> a0;
        const expr *b0;
      };

      struct _after_expr_rect_in_Mul_2 {
        std::shared_ptr<expr> a0;
        const expr *b0;
        T1 _tmp4;
      };

      using _frame =
          std::variant<_call, _after_expr_rect_in_Add,
                       _after_expr_rect_in_Add_2, _after_expr_rect_in_If0,
                       _after_expr_rect_in_If0_2, _after_expr_rect_in_If0_3,
                       _after_expr_rect_in_Let, _after_expr_rect_in_Let_2,
                       _after_expr_rect_in_Mul, _after_expr_rect_in_Mul_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Num>(_sv.v())) {
            const auto &[n0] = std::get<typename expr::Num>(_sv.v());
            _result = f(n0);
          } else if (std::holds_alternative<typename expr::Var>(_sv.v())) {
            const auto &[i0] = std::get<typename expr::Var>(_sv.v());
            _result = f0(i0);
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, b0] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Add{a0, crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, b0] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Mul{a0, crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Let>(_sv.v())) {
            const auto &[e1, body0] = std::get<typename expr::Let>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Let{e1, crane_raw(body0)});
            _stack.emplace_back(_call{crane_raw(e1)});
          } else {
            const auto &[c0, t0, e1] = std::get<typename expr::If0>(_sv.v());
            _stack.emplace_back(
                _after_expr_rect_in_If0{c0, crane_raw(t0), crane_raw(e1)});
            _stack.emplace_back(_call{crane_raw(c0)});
          }
        } else if (std::holds_alternative<_after_expr_rect_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Add>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &b0 = *_f.b0;
          _stack.emplace_back(
              _after_expr_rect_in_Add_2{std::move(a0), &b0,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else if (std::holds_alternative<_after_expr_rect_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Add_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &b0 = *_f.b0;
          _result = f1(*a0, std::move(_f._tmp2), b0, std::move(_result));
        } else if (std::holds_alternative<_after_expr_rect_in_If0>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_If0>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> c0 = std::move(_f.c0);
          const expr &t0 = *_f.t0;
          const expr &e1 = *_f.e1;
          _stack.emplace_back(_after_expr_rect_in_If0_2{std::move(c0), &t0, &e1,
                                                        std::move(_result)});
          _stack.emplace_back(_call{_f.t0});
        } else if (std::holds_alternative<_after_expr_rect_in_If0_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_If0_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> c0 = std::move(_f.c0);
          const expr &t0 = *_f.t0;
          const expr &e1 = *_f.e1;
          _stack.emplace_back(_after_expr_rect_in_If0_3{
              std::move(c0), &t0, &e1, std::move(_f._tmp9),
              std::move(_result)});
          _stack.emplace_back(_call{_f.e1});
        } else if (std::holds_alternative<_after_expr_rect_in_If0_3>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_If0_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> c0 = std::move(_f.c0);
          const expr &t0 = *_f.t0;
          const expr &e1 = *_f.e1;
          _result = f4(*c0, std::move(_f._tmp9), t0, std::move(_f._tmp8), e1,
                       std::move(_result));
        } else if (std::holds_alternative<_after_expr_rect_in_Let>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Let>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> e1 = std::move(_f.e1);
          const expr &body0 = *_f.body0;
          _stack.emplace_back(_after_expr_rect_in_Let_2{std::move(e1), &body0,
                                                        std::move(_result)});
          _stack.emplace_back(_call{_f.body0});
        } else if (std::holds_alternative<_after_expr_rect_in_Let_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Let_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> e1 = std::move(_f.e1);
          const expr &body0 = *_f.body0;
          _result = f3(*e1, std::move(_f._tmp6), body0, std::move(_result));
        } else if (std::holds_alternative<_after_expr_rect_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Mul>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &b0 = *_f.b0;
          _stack.emplace_back(
              _after_expr_rect_in_Mul_2{std::move(a0), &b0,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else {
          auto _f = std::move(std::get<_after_expr_rect_in_Mul_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &b0 = *_f.b0;
          _result = f2(*a0, std::move(_f._tmp4), b0, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t lookup(const List<uint64_t> &env, uint64_t i);

  struct instr {
    // TYPES
    struct IPush {
      uint64_t n;
    };

    struct ILoad {
      uint64_t i;
    };

    struct IAdd {};

    struct IMul {};

    struct IBind {};

    struct IUnbind {};

    using variant_t = std::variant<IPush, ILoad, IAdd, IMul, IBind, IUnbind>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr() {}

    explicit instr(IPush _v) : v_(std::move(_v)) {}

    explicit instr(ILoad _v) : v_(std::move(_v)) {}

    explicit instr(IAdd _v) : v_(_v) {}

    explicit instr(IMul _v) : v_(_v) {}

    explicit instr(IBind _v) : v_(_v) {}

    explicit instr(IUnbind _v) : v_(_v) {}

    static instr ipush(uint64_t n) { return instr(IPush{n}); }

    static instr iload(uint64_t i) { return instr(ILoad{i}); }

    static instr iadd() { return instr(IAdd{}); }

    static instr imul() { return instr(IMul{}); }

    static instr ibind() { return instr(IBind{}); }

    static instr iunbind() { return instr(IUnbind{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
    T1 instr_rec(F0 &&f, F1 &&f0, T1 f1, T1 f2, T1 f3, T1 f4) const {
      return this->template instr_rect<T1>(f, f0, std::move(f1), std::move(f2),
                                           std::move(f3), std::move(f4));
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const uint64_t &>
    T1 instr_rect(F0 &&f, F1 &&f0, T1 f1, T1 f2, T1 f3, T1 f4) const {
      if (std::holds_alternative<typename instr::IPush>(this->v())) {
        const auto &[n0] = std::get<typename instr::IPush>(this->v());
        return f(n0);
      } else if (std::holds_alternative<typename instr::ILoad>(this->v())) {
        const auto &[i1] = std::get<typename instr::ILoad>(this->v());
        return f0(i1);
      } else if (std::holds_alternative<typename instr::IAdd>(this->v())) {
        return f1;
      } else if (std::holds_alternative<typename instr::IMul>(this->v())) {
        return f2;
      } else if (std::holds_alternative<typename instr::IBind>(this->v())) {
        return f3;
      } else {
        return f4;
      }
    }
  };

  static List<instr> compile(const expr &e, const List<instr> &k);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &,
                                   const uint64_t &>
  static List<uint64_t> binop(F0 &&op, const List<uint64_t> &s) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(s.v())) {
      return s;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(s.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        return s;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        return List<uint64_t>::cons(op(a00, a0), crane::shared_child(a10));
      }
    }
  }

  static uint64_t run(uint64_t fuel, const List<instr> &code,
                      const List<uint64_t> &stack, const List<uint64_t> &env);
  static expr gen(uint64_t depth, uint64_t s);
  static uint64_t round(uint64_t depth, uint64_t i);
  static uint64_t interp(uint64_t depth, uint64_t rounds);
};

#endif // INCLUDED_GB_INTERP
