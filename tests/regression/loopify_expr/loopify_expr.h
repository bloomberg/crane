#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

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
      std::shared_ptr<expr> a0;
    };

    struct Add {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct Mul {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct Cond {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
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

    static expr val(uint64_t a0) { return expr(Val{a0}); }

    static expr succ(expr a0) {
      return expr(Succ{std::make_shared<expr>(std::move(a0))});
    }

    static expr add(expr a0, expr a1) {
      return expr(Add{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    static expr mul(expr a0, expr a1) {
      return expr(Mul{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    static expr cond(expr a0, expr a1, expr a2) {
      return expr(Cond{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1)),
                       std::make_shared<expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~expr() {
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Succ>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Mul>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Cond>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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
    expr(expr &&) noexcept = default;
    expr &operator=(expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    expr simplify() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Cond: saves [a1, a0], dispatches next recursive call.
      struct _After_Cond {
        const expr *a1;
        const expr *a0;
      };

      /// _After_Cond_1: saves [_result, a0], dispatches next recursive call.
      struct _After_Cond_1 {
        expr _result;
        const expr *a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        expr _result_0;
        expr _result_1;
      };

      /// _Cont_Add: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add_1 {
        expr s1;
      };

      /// _Cont_Add_2: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add_2 {
        expr s1;
      };

      /// _Cont_Cond: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Cond {
        expr s1;
      };

      /// _Cont_Cond_1: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Cond_1 {
        expr s1;
      };

      /// _Cont_Mul: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul {
        expr s1;
      };

      /// _Cont_Mul_1: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul_1 {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_2: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul_2 {
        expr s1;
      };

      /// _Cont_Succ: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Succ {
        expr s1;
      };

      /// _Cont_Succ_1: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Succ_1 {
        expr s1;
      };

      /// _Cont__x: saves [a00], resumes after recursive call, then processes
      /// rest.
      struct _Cont__x {
        uint64_t a00;
      };

      /// _Cont_n0: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_n0 {
        expr s1;
      };

      /// _Resume_Succ: resumes after recursive call with _result.
      struct _Resume_Succ {};

      using _Frame =
          std::variant<_Enter, _After_Cond, _After_Cond_1, _Combine_Cond,
                       _Cont_Add, _Cont_Add_1, _Cont_Add_2, _Cont_Cond,
                       _Cont_Cond_1, _Cont_Mul, _Cont_Mul_1, _Cont_Mul_2,
                       _Cont_Succ, _Cont_Succ_1, _Cont__x, _Cont_n0,
                       _Resume_Succ>;
      expr _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simplify: _Enter -> _After_Cond -> _After_Cond_1 ->
      /// _Combine_Cond -> _Cont_Add -> _Cont_Add_1 -> _Cont_Add_2 -> _Cont_Cond
      /// -> _Cont_Cond_1 -> _Cont_Mul -> _Cont_Mul_1 -> _Cont_Mul_2 ->
      /// _Cont_Succ -> _Cont_Succ_1 -> _Cont__x -> _Cont_n0 -> _Resume_Succ.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = expr::val(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume_Succ{});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul_1{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{crane_raw(a1), crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{std::move(_result), _f.a0});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(
              _Combine_Cond{std::move(_f._result), std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_Cond>(_frame)) {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result = expr::cond(std::move(_result), std::move(_f._result_1),
                               std::move(_f._result_0));
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          expr r_ = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_.v_mut())) {
            auto &[a00] = std::get<typename expr::Val>(r_.v_mut());
            if (a00 <= 0) {
              _stack.emplace_back(_Enter{crane_raw(a1)});
            } else {
              uint64_t n0 = a00 - 1;
              expr s1 = expr::val((n0 + 1));
              _stack.emplace_back(_Cont_n0{std::move(s1)});
              _stack.emplace_back(_Enter{crane_raw(a1)});
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_.v_mut())) {
            auto &[a00] = std::get<typename expr::Succ>(r_.v_mut());
            expr s1 = expr::succ(*a00);
            _stack.emplace_back(_Cont_Succ{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Add>(r_.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Add>(r_.v_mut());
            expr s1 = expr::add(*a00, *a10);
            _stack.emplace_back(_Cont_Add_1{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Mul>(r_.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Mul>(r_.v_mut());
            expr s1 = expr::mul(*a00, *a10);
            _stack.emplace_back(_Cont_Mul{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            auto &[a00, a10, a20] = std::get<typename expr::Cond>(r_.v_mut());
            expr s1 = expr::cond(*a00, *a10, *a20);
            _stack.emplace_back(_Cont_Cond{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Add_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_2>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                _result = std::move(s1);
              } else {
                _result = expr::mul(std::move(s1), expr::val(std::move(a01)));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_1>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                _result = std::move(s1);
              } else {
                _result = expr::mul(std::move(s1), expr::val(std::move(a01)));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          expr r_ = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_.v_mut())) {
            auto &[a00] = std::get<typename expr::Val>(r_.v_mut());
            if (a00 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a00 - 1;
              _stack.emplace_back(_Cont__x{a00});
              _stack.emplace_back(_Enter{crane_raw(a1)});
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_.v_mut())) {
            auto &[a00] = std::get<typename expr::Succ>(r_.v_mut());
            expr s1 = expr::succ(*a00);
            _stack.emplace_back(_Cont_Succ_1{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Add>(r_.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Add>(r_.v_mut());
            expr s1 = expr::add(*a00, *a10);
            _stack.emplace_back(_Cont_Add_2{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Mul>(r_.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Mul>(r_.v_mut());
            expr s1 = expr::mul(*a00, *a10);
            _stack.emplace_back(_Cont_Mul_2{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            auto &[a00, a10, a20] = std::get<typename expr::Cond>(r_.v_mut());
            expr s1 = expr::cond(*a00, *a10, *a20);
            _stack.emplace_back(_Cont_Cond_1{std::move(s1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_Cont_Mul_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_2>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                _result = std::move(s1);
              } else {
                _result = expr::mul(std::move(s1), expr::val(std::move(a01)));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Succ>(_frame)) {
          auto _f = std::move(std::get<_Cont_Succ>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont_Succ_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Succ_1>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                _result = std::move(s1);
              } else {
                _result = expr::mul(std::move(s1), expr::val(std::move(a01)));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<_Cont__x>(_frame)) {
          auto _f = std::move(std::get<_Cont__x>(_frame));
          uint64_t a00 = _f.a00;
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t n1 = a01 - 1;
              expr s2 = expr::val((n1 + 1));
              if (a00 == UINT64_C(1)) {
                _result = std::move(s2);
              } else {
                _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            expr s2 = expr::succ(*a01);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            expr s2 = expr::add(*a01, *a11);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            expr s2 = expr::mul(*a01, *a11);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            expr s2 = expr::cond(*a01, *a11, *a21);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          }
        } else if (std::holds_alternative<_Cont_n0>(_frame)) {
          auto _f = std::move(std::get<_Cont_n0>(_frame));
          expr s1 = std::move(_f.s1);
          expr r_0 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(r_0.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n2 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n2 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(r_0.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(r_0.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] = std::get<typename expr::Cond>(r_0.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = expr::succ(std::move(_result));
        }
      }
      return _result;
    }

    /// size e counts total number of nodes.
    uint64_t size() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _Cont_Add: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add_1 {
        uint64_t r_;
      };

      /// _Cont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// _Cont_Cond_1: saves [a2, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond_1 {
        std::shared_ptr<expr> a2;
        uint64_t r_;
      };

      /// _Cont_Cond_2: saves [r_, r_0], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond_2 {
        uint64_t r_;
        uint64_t r_0;
      };

      /// _Cont_Mul: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul_1 {
        uint64_t r_;
      };

      /// _Resume_Succ: resumes after recursive call with _result.
      struct _Resume_Succ {};

      using _Frame =
          std::variant<_Enter, _Cont_Add, _Cont_Add_1, _Cont_Cond, _Cont_Cond_1,
                       _Cont_Cond_2, _Cont_Mul, _Cont_Mul_1, _Resume_Succ>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified size: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_Cond ->
      /// _Cont_Cond_1 -> _Cont_Cond_2 -> _Cont_Mul -> _Cont_Mul_1 ->
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
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Add_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = ((r_ + r_0) + 1);
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Cond_1{std::move(a2), r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_1>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _stack.emplace_back(_Cont_Cond_2{r_, r_0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_2>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = _f.r_0;
          uint64_t r_1 = std::move(_result);
          _result = ((r_ + (r_0 + r_1)) + 1);
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Mul_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = ((r_ + r_0) + 1);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = (std::move(_result) + 1);
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

      /// _Cont_Add: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add_1 {
        uint64_t r_;
      };

      /// _Cont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// _Cont_Cond_1: saves [a2, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond_1 {
        std::shared_ptr<expr> a2;
        uint64_t r_;
      };

      /// _Cont_Cond_2: saves [r_, r_0], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond_2 {
        uint64_t r_;
        uint64_t r_0;
      };

      /// _Cont_Mul: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul_1 {
        uint64_t r_;
      };

      using _Frame =
          std::variant<_Enter, _Cont_Add, _Cont_Add_1, _Cont_Cond, _Cont_Cond_1,
                       _Cont_Cond_2, _Cont_Mul, _Cont_Mul_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified count_vals: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_Cond
      /// -> _Cont_Cond_1 -> _Cont_Cond_2 -> _Cont_Mul -> _Cont_Mul_1.
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
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Add_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (r_ + r_0);
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Cond_1{std::move(a2), r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_1>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _stack.emplace_back(_Cont_Cond_2{r_, r_0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_2>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = _f.r_0;
          uint64_t r_1 = std::move(_result);
          _result = (r_ + (r_0 + r_1));
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Mul_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (r_ + r_0);
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

      /// _Cont_Add: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add_1 {
        uint64_t r_;
      };

      /// _Cont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// _Cont_Cond_1: saves [a2, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond_1 {
        std::shared_ptr<expr> a2;
        uint64_t r_;
      };

      /// _Cont_Cond_2: saves [r_, r_0], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond_2 {
        uint64_t r_;
        uint64_t r_0;
      };

      /// _Cont_Mul: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul_1 {
        uint64_t r_;
      };

      /// _Resume_Succ: resumes after recursive call with _result.
      struct _Resume_Succ {};

      using _Frame =
          std::variant<_Enter, _Cont_Add, _Cont_Add_1, _Cont_Cond, _Cont_Cond_1,
                       _Cont_Cond_2, _Cont_Mul, _Cont_Mul_1, _Resume_Succ>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified depth: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_Cond ->
      /// _Cont_Cond_1 -> _Cont_Cond_2 -> _Cont_Mul -> _Cont_Mul_1 ->
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
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Add_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (std::max(r_, r_0) + 1);
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Cond_1{std::move(a2), r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_1>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _stack.emplace_back(_Cont_Cond_2{r_, r_0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_2>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = _f.r_0;
          uint64_t r_1 = std::move(_result);
          _result = (std::max(r_, std::max(r_0, r_1)) + 1);
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Mul_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (std::max(r_, r_0) + 1);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    uint64_t eval() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _Cont_Add: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Add_1 {
        uint64_t r_;
      };

      /// _Cont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// _Cont_Mul: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Mul_1 {
        uint64_t r_;
      };

      /// _Resume_Succ: resumes after recursive call with _result.
      struct _Resume_Succ {};

      using _Frame = std::variant<_Enter, _Cont_Add, _Cont_Add_1, _Cont_Cond,
                                  _Cont_Mul, _Cont_Mul_1, _Resume_Succ>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_Cond ->
      /// _Cont_Mul -> _Cont_Mul_1 -> _Resume_Succ.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Resume_Succ{});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Add_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (r_ + r_0);
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          if (UINT64_C(0) < r_) {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Mul_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (r_ * r_0);
        } else {
          auto _f = std::move(std::get<_Resume_Succ>(_frame));
          _result = (std::move(_result) + 1);
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
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _Cont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Add_1 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        T1 r_;
      };

      /// _Cont_Cond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// _Cont_Cond_1: saves [a0, a1, a2, r_], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Cond_1 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
        T1 r_;
      };

      /// _Cont_Cond_2: saves [a0, a1, a2, r_, r_0], resumes after recursive
      /// call, then processes rest.
      struct _Cont_Cond_2 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
        T1 r_;
        T1 r_0;
      };

      /// _Cont_Mul: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Mul {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Mul_1 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        T1 r_;
      };

      /// _Cont_Succ: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Succ {
        std::shared_ptr<expr> a0;
      };

      using _Frame =
          std::variant<_Enter, _Cont_Add, _Cont_Add_1, _Cont_Cond, _Cont_Cond_1,
                       _Cont_Cond_2, _Cont_Mul, _Cont_Mul_1, _Cont_Succ>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rec: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_Cond
      /// -> _Cont_Cond_1 -> _Cont_Cond_2 -> _Cont_Mul -> _Cont_Mul_1 ->
      /// _Cont_Succ.
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
            _stack.emplace_back(_Cont_Succ{a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_Add_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f1(*a0, std::move(r_), *a1, std::move(r_0));
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          T1 r_ = std::move(_result);
          _stack.emplace_back(
              _Cont_Cond_1{std::move(a0), a1, std::move(a2), std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _stack.emplace_back(_Cont_Cond_2{std::move(a0), std::move(a1), a2,
                                           std::move(r_), std::move(r_0)});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_2>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          auto r_0 = std::move(_f.r_0);
          T1 r_1 = std::move(_result);
          _result =
              f3(*a0, std::move(r_), *a1, std::move(r_0), *a2, std::move(r_1));
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_Mul_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f2(*a0, std::move(r_), *a1, std::move(r_0));
        } else {
          auto _f = std::move(std::get<_Cont_Succ>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          T1 r_ = std::move(_result);
          _result = f0(*a0, std::move(r_));
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

      /// _Cont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Add {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Add_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Add_1 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        T1 r_;
      };

      /// _Cont_Cond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// _Cont_Cond_1: saves [a0, a1, a2, r_], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Cond_1 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
        T1 r_;
      };

      /// _Cont_Cond_2: saves [a0, a1, a2, r_, r_0], resumes after recursive
      /// call, then processes rest.
      struct _Cont_Cond_2 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
        T1 r_;
        T1 r_0;
      };

      /// _Cont_Mul: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Mul {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// _Cont_Mul_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Mul_1 {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        T1 r_;
      };

      /// _Cont_Succ: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Succ {
        std::shared_ptr<expr> a0;
      };

      using _Frame =
          std::variant<_Enter, _Cont_Add, _Cont_Add_1, _Cont_Cond, _Cont_Cond_1,
                       _Cont_Cond_2, _Cont_Mul, _Cont_Mul_1, _Cont_Succ>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rect: _Enter -> _Cont_Add -> _Cont_Add_1 -> _Cont_Cond
      /// -> _Cont_Cond_1 -> _Cont_Cond_2 -> _Cont_Mul -> _Cont_Mul_1 ->
      /// _Cont_Succ.
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
            _stack.emplace_back(_Cont_Succ{a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Cont_Add{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Cont_Mul{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Add>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_Add_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Add_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Add_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f1(*a0, std::move(r_), *a1, std::move(r_0));
        } else if (std::holds_alternative<_Cont_Cond>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          T1 r_ = std::move(_result);
          _stack.emplace_back(
              _Cont_Cond_1{std::move(a0), a1, std::move(a2), std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _stack.emplace_back(_Cont_Cond_2{std::move(a0), std::move(a1), a2,
                                           std::move(r_), std::move(r_0)});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Cond_2>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          auto r_0 = std::move(_f.r_0);
          T1 r_1 = std::move(_result);
          _result =
              f3(*a0, std::move(r_), *a1, std::move(r_0), *a2, std::move(r_1));
        } else if (std::holds_alternative<_Cont_Mul>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_Mul_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Mul_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f2(*a0, std::move(r_), *a1, std::move(r_0));
        } else {
          auto _f = std::move(std::get<_Cont_Succ>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          T1 r_ = std::move(_result);
          _result = f0(*a0, std::move(r_));
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
      std::shared_ptr<simple_expr> a0;
      std::shared_ptr<simple_expr> a1;
    };

    struct IfPos {
      std::shared_ptr<simple_expr> a0;
      std::shared_ptr<simple_expr> a1;
      std::shared_ptr<simple_expr> a2;
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

    static simple_expr lit(uint64_t a0) { return simple_expr(Lit{a0}); }

    static simple_expr plus(simple_expr a0, simple_expr a1) {
      return simple_expr(Plus{std::make_shared<simple_expr>(std::move(a0)),
                              std::make_shared<simple_expr>(std::move(a1))});
    }

    static simple_expr ifpos(simple_expr a0, simple_expr a1, simple_expr a2) {
      return simple_expr(IfPos{std::make_shared<simple_expr>(std::move(a0)),
                               std::make_shared<simple_expr>(std::move(a1)),
                               std::make_shared<simple_expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~simple_expr() {
      crane::small_vector<std::shared_ptr<simple_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Plus>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<IfPos>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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

    simple_expr(const simple_expr &) = default;
    simple_expr &operator=(const simple_expr &) = default;
    simple_expr(simple_expr &&) noexcept = default;
    simple_expr &operator=(simple_expr &&) noexcept = default;

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

      /// _Cont_IfPos: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_IfPos {
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// _Cont_IfPos_1: saves [a2, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_IfPos_1 {
        std::shared_ptr<simple_expr> a2;
        uint64_t r_;
      };

      /// _Cont_IfPos_2: saves [r_, r_0], resumes after recursive call, then
      /// processes rest.
      struct _Cont_IfPos_2 {
        uint64_t r_;
        uint64_t r_0;
      };

      /// _Cont_Plus: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Plus {
        std::shared_ptr<simple_expr> a1;
      };

      /// _Cont_Plus_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Plus_1 {
        uint64_t r_;
      };

      using _Frame = std::variant<_Enter, _Cont_IfPos, _Cont_IfPos_1,
                                  _Cont_IfPos_2, _Cont_Plus, _Cont_Plus_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified depth_simple: _Enter -> _Cont_IfPos -> _Cont_IfPos_1 ->
      /// _Cont_IfPos_2 -> _Cont_Plus -> _Cont_Plus_1.
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
            _stack.emplace_back(_Cont_Plus{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_Cont_IfPos{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_IfPos_1{std::move(a2), r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos_1>(_frame));
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _stack.emplace_back(_Cont_IfPos_2{r_, r_0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_IfPos_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos_2>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = _f.r_0;
          uint64_t r_1 = std::move(_result);
          _result = (std::max(r_, std::max(r_0, r_1)) + 1);
        } else if (std::holds_alternative<_Cont_Plus>(_frame)) {
          auto _f = std::move(std::get<_Cont_Plus>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Plus_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_Plus_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (std::max(r_, r_0) + 1);
        }
      }
      return _result;
    }

    /// eval_simple e evaluates simple expression with positive test.
    uint64_t eval_simple() const {
      const simple_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_expr *_self;
      };

      /// _Cont_IfPos: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_IfPos {
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// _Cont_Plus: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Plus {
        std::shared_ptr<simple_expr> a1;
      };

      /// _Cont_Plus_1: saves [r_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Plus_1 {
        uint64_t r_;
      };

      using _Frame =
          std::variant<_Enter, _Cont_IfPos, _Cont_Plus, _Cont_Plus_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_simple: _Enter -> _Cont_IfPos -> _Cont_Plus ->
      /// _Cont_Plus_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_Cont_Plus{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_Cont_IfPos{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          if (UINT64_C(0) < r_) {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_Cont_Plus>(_frame)) {
          auto _f = std::move(std::get<_Cont_Plus>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_Plus_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_Plus_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (r_ + r_0);
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
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_expr *_self;
      };

      /// _Cont_IfPos: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_IfPos {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// _Cont_IfPos_1: saves [a0, a1, a2, r_], resumes after recursive call,
      /// then processes rest.
      struct _Cont_IfPos_1 {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
        T1 r_;
      };

      /// _Cont_IfPos_2: saves [a0, a1, a2, r_, r_0], resumes after recursive
      /// call, then processes rest.
      struct _Cont_IfPos_2 {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
        T1 r_;
        T1 r_0;
      };

      /// _Cont_Plus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Plus {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
      };

      /// _Cont_Plus_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Plus_1 {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        T1 r_;
      };

      using _Frame = std::variant<_Enter, _Cont_IfPos, _Cont_IfPos_1,
                                  _Cont_IfPos_2, _Cont_Plus, _Cont_Plus_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_expr_rec: _Enter -> _Cont_IfPos -> _Cont_IfPos_1 ->
      /// _Cont_IfPos_2 -> _Cont_Plus -> _Cont_Plus_1.
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
            _stack.emplace_back(_Cont_Plus{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_Cont_IfPos{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          T1 r_ = std::move(_result);
          _stack.emplace_back(
              _Cont_IfPos_1{std::move(a0), a1, std::move(a2), std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _stack.emplace_back(_Cont_IfPos_2{std::move(a0), std::move(a1), a2,
                                            std::move(r_), std::move(r_0)});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_IfPos_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos_2>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          auto r_0 = std::move(_f.r_0);
          T1 r_1 = std::move(_result);
          _result =
              f1(*a0, std::move(r_), *a1, std::move(r_0), *a2, std::move(r_1));
        } else if (std::holds_alternative<_Cont_Plus>(_frame)) {
          auto _f = std::move(std::get<_Cont_Plus>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_Plus_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_Plus_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f0(*a0, std::move(r_), *a1, std::move(r_0));
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

      /// _Cont_IfPos: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_IfPos {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// _Cont_IfPos_1: saves [a0, a1, a2, r_], resumes after recursive call,
      /// then processes rest.
      struct _Cont_IfPos_1 {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
        T1 r_;
      };

      /// _Cont_IfPos_2: saves [a0, a1, a2, r_, r_0], resumes after recursive
      /// call, then processes rest.
      struct _Cont_IfPos_2 {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
        T1 r_;
        T1 r_0;
      };

      /// _Cont_Plus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Plus {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
      };

      /// _Cont_Plus_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Plus_1 {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        T1 r_;
      };

      using _Frame = std::variant<_Enter, _Cont_IfPos, _Cont_IfPos_1,
                                  _Cont_IfPos_2, _Cont_Plus, _Cont_Plus_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_expr_rect: _Enter -> _Cont_IfPos -> _Cont_IfPos_1 ->
      /// _Cont_IfPos_2 -> _Cont_Plus -> _Cont_Plus_1.
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
            _stack.emplace_back(_Cont_Plus{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_Cont_IfPos{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_IfPos>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          T1 r_ = std::move(_result);
          _stack.emplace_back(
              _Cont_IfPos_1{std::move(a0), a1, std::move(a2), std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _stack.emplace_back(_Cont_IfPos_2{std::move(a0), std::move(a1), a2,
                                            std::move(r_), std::move(r_0)});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_IfPos_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_IfPos_2>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          auto r_0 = std::move(_f.r_0);
          T1 r_1 = std::move(_result);
          _result =
              f1(*a0, std::move(r_), *a1, std::move(r_0), *a2, std::move(r_1));
        } else if (std::holds_alternative<_Cont_Plus>(_frame)) {
          auto _f = std::move(std::get<_Cont_Plus>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_Plus_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_Plus_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f0(*a0, std::move(r_), *a1, std::move(r_0));
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
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
    };

    struct CCond {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
      std::shared_ptr<cond_expr> a2;
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

    static cond_expr clit(uint64_t a0) { return cond_expr(CLit{a0}); }

    static cond_expr cplus(cond_expr a0, cond_expr a1) {
      return cond_expr(CPlus{std::make_shared<cond_expr>(std::move(a0)),
                             std::make_shared<cond_expr>(std::move(a1))});
    }

    static cond_expr ccond(cond_expr a0, cond_expr a1, cond_expr a2) {
      return cond_expr(CCond{std::make_shared<cond_expr>(std::move(a0)),
                             std::make_shared<cond_expr>(std::move(a1)),
                             std::make_shared<cond_expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~cond_expr() {
      crane::small_vector<std::shared_ptr<cond_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<CPlus>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<CCond>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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

    cond_expr(const cond_expr &) = default;
    cond_expr &operator=(const cond_expr &) = default;
    cond_expr(cond_expr &&) noexcept = default;
    cond_expr &operator=(cond_expr &&) noexcept = default;

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

      /// _Cont_CCond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CCond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// _Cont_CCond_1: saves [a2, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CCond_1 {
        std::shared_ptr<cond_expr> a2;
        uint64_t r_;
      };

      /// _Cont_CCond_2: saves [r_, r_0], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CCond_2 {
        uint64_t r_;
        uint64_t r_0;
      };

      /// _Cont_CPlus: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_CPlus {
        std::shared_ptr<cond_expr> a1;
      };

      /// _Cont_CPlus_1: saves [r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CPlus_1 {
        uint64_t r_;
      };

      using _Frame = std::variant<_Enter, _Cont_CCond, _Cont_CCond_1,
                                  _Cont_CCond_2, _Cont_CPlus, _Cont_CPlus_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified depth_cond: _Enter -> _Cont_CCond -> _Cont_CCond_1 ->
      /// _Cont_CCond_2 -> _Cont_CPlus -> _Cont_CPlus_1.
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
            _stack.emplace_back(_Cont_CPlus{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_Cont_CCond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_CCond>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_CCond_1{std::move(a2), r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_CCond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond_1>(_frame));
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _stack.emplace_back(_Cont_CCond_2{r_, r_0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_CCond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond_2>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = _f.r_0;
          uint64_t r_1 = std::move(_result);
          _result = (std::max(r_, std::max(r_0, r_1)) + 1);
        } else if (std::holds_alternative<_Cont_CPlus>(_frame)) {
          auto _f = std::move(std::get<_Cont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_CPlus_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_CPlus_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (std::max(r_, r_0) + 1);
        }
      }
      return _result;
    }

    /// eval_cond e evaluates conditional expression.
    uint64_t eval_cond() const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _Cont_CCond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CCond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// _Cont_CPlus: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_CPlus {
        std::shared_ptr<cond_expr> a1;
      };

      /// _Cont_CPlus_1: saves [r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CPlus_1 {
        uint64_t r_;
      };

      using _Frame =
          std::variant<_Enter, _Cont_CCond, _Cont_CPlus, _Cont_CPlus_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_cond: _Enter -> _Cont_CCond -> _Cont_CPlus ->
      /// _Cont_CPlus_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_Cont_CPlus{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_Cont_CCond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_CCond>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          uint64_t r_ = std::move(_result);
          if (UINT64_C(0) < r_) {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_Cont_CPlus>(_frame)) {
          auto _f = std::move(std::get<_Cont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          uint64_t r_ = std::move(_result);
          _stack.emplace_back(_Cont_CPlus_1{r_});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_CPlus_1>(_frame));
          uint64_t r_ = _f.r_;
          uint64_t r_0 = std::move(_result);
          _result = (r_ + r_0);
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
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _Cont_CCond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CCond {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// _Cont_CCond_1: saves [a0, a1, a2, r_], resumes after recursive call,
      /// then processes rest.
      struct _Cont_CCond_1 {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
        T1 r_;
      };

      /// _Cont_CCond_2: saves [a0, a1, a2, r_, r_0], resumes after recursive
      /// call, then processes rest.
      struct _Cont_CCond_2 {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
        T1 r_;
        T1 r_0;
      };

      /// _Cont_CPlus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CPlus {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      /// _Cont_CPlus_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CPlus_1 {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        T1 r_;
      };

      using _Frame = std::variant<_Enter, _Cont_CCond, _Cont_CCond_1,
                                  _Cont_CCond_2, _Cont_CPlus, _Cont_CPlus_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rec: _Enter -> _Cont_CCond -> _Cont_CCond_1 ->
      /// _Cont_CCond_2 -> _Cont_CPlus -> _Cont_CPlus_1.
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
            _stack.emplace_back(_Cont_CPlus{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_Cont_CCond{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_CCond>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          T1 r_ = std::move(_result);
          _stack.emplace_back(
              _Cont_CCond_1{std::move(a0), a1, std::move(a2), std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_CCond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _stack.emplace_back(_Cont_CCond_2{std::move(a0), std::move(a1), a2,
                                            std::move(r_), std::move(r_0)});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_CCond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond_2>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          auto r_0 = std::move(_f.r_0);
          T1 r_1 = std::move(_result);
          _result =
              f1(*a0, std::move(r_), *a1, std::move(r_0), *a2, std::move(r_1));
        } else if (std::holds_alternative<_Cont_CPlus>(_frame)) {
          auto _f = std::move(std::get<_Cont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_CPlus_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_CPlus_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f0(*a0, std::move(r_), *a1, std::move(r_0));
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

      /// _Cont_CCond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CCond {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// _Cont_CCond_1: saves [a0, a1, a2, r_], resumes after recursive call,
      /// then processes rest.
      struct _Cont_CCond_1 {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
        T1 r_;
      };

      /// _Cont_CCond_2: saves [a0, a1, a2, r_, r_0], resumes after recursive
      /// call, then processes rest.
      struct _Cont_CCond_2 {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
        T1 r_;
        T1 r_0;
      };

      /// _Cont_CPlus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CPlus {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      /// _Cont_CPlus_1: saves [a0, a1, r_], resumes after recursive call, then
      /// processes rest.
      struct _Cont_CPlus_1 {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        T1 r_;
      };

      using _Frame = std::variant<_Enter, _Cont_CCond, _Cont_CCond_1,
                                  _Cont_CCond_2, _Cont_CPlus, _Cont_CPlus_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rect: _Enter -> _Cont_CCond -> _Cont_CCond_1 ->
      /// _Cont_CCond_2 -> _Cont_CPlus -> _Cont_CPlus_1.
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
            _stack.emplace_back(_Cont_CPlus{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_Cont_CCond{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_CCond>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          T1 r_ = std::move(_result);
          _stack.emplace_back(
              _Cont_CCond_1{std::move(a0), a1, std::move(a2), std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_CCond_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _stack.emplace_back(_Cont_CCond_2{std::move(a0), std::move(a1), a2,
                                            std::move(r_), std::move(r_0)});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_CCond_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_CCond_2>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          auto r_ = std::move(_f.r_);
          auto r_0 = std::move(_f.r_0);
          T1 r_1 = std::move(_result);
          _result =
              f1(*a0, std::move(r_), *a1, std::move(r_0), *a2, std::move(r_1));
        } else if (std::holds_alternative<_Cont_CPlus>(_frame)) {
          auto _f = std::move(std::get<_Cont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          T1 r_ = std::move(_result);
          _stack.emplace_back(_Cont_CPlus_1{std::move(a0), a1, std::move(r_)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_CPlus_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          auto r_ = std::move(_f.r_);
          T1 r_0 = std::move(_result);
          _result = f0(*a0, std::move(r_), *a1, std::move(r_0));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
