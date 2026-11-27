#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <cstdint>
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

    static expr succ(crane::shared_child_slot<expr> a0) {
      return expr(Succ{a0.take()});
    }

    static expr add(crane::shared_child_slot<expr> a0,
                    crane::shared_child_slot<expr> a1) {
      return expr(Add{a0.take(), a1.take()});
    }

    static expr mul(crane::shared_child_slot<expr> a0,
                    crane::shared_child_slot<expr> a1) {
      return expr(Mul{a0.take(), a1.take()});
    }

    static expr cond(crane::shared_child_slot<expr> a0,
                     crane::shared_child_slot<expr> a1,
                     crane::shared_child_slot<expr> a2) {
      return expr(Cond{a0.take(), a1.take(), a2.take()});
    }

    // MANIPULATORS
    ~expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Val>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Succ>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Add>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Mul>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Cond>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
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
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    expr simplify() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of simplify: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_simplify_in_Add {
        const expr *a1;
      };

      struct _after_simplify_in_Add_2 {
        expr s1;
      };

      struct _after_simplify_in_Add_3 {
        expr s1;
      };

      struct _after_simplify_in_Cond {
        expr s1;
      };

      struct _after_simplify_in_Cond_2 {
        expr s1;
      };

      struct _after_simplify_in_Cond_3 {
        const expr *a1;
        const expr *a2;
      };

      struct _after_simplify_in_Cond_4 {
        const expr *a2;
        expr _tmp16;
      };

      struct _after_simplify_in_Cond_5 {
        expr _tmp16;
        expr _tmp15;
      };

      struct _after_simplify_in_Mul {
        expr s1;
      };

      struct _after_simplify_in_Mul_2 {
        const expr *a1;
      };

      struct _after_simplify_in_Mul_3 {
        expr s1;
      };

      struct _after_simplify_in_S {
        expr s1;
      };

      struct _after_simplify_in_S_2 {
        uint64_t a00;
      };

      struct _after_simplify_in_Succ {};

      struct _after_simplify_in_Succ_2 {
        expr s1;
      };

      struct _after_simplify_in_Succ_3 {
        expr s1;
      };

      using _frame =
          std::variant<_call, _after_simplify_in_Add, _after_simplify_in_Add_2,
                       _after_simplify_in_Add_3, _after_simplify_in_Cond,
                       _after_simplify_in_Cond_2, _after_simplify_in_Cond_3,
                       _after_simplify_in_Cond_4, _after_simplify_in_Cond_5,
                       _after_simplify_in_Mul, _after_simplify_in_Mul_2,
                       _after_simplify_in_Mul_3, _after_simplify_in_S,
                       _after_simplify_in_S_2, _after_simplify_in_Succ,
                       _after_simplify_in_Succ_2, _after_simplify_in_Succ_3>;
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
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = expr::val(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_after_simplify_in_Succ{});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_simplify_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_simplify_in_Mul_2{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_simplify_in_Cond_3{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_simplify_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          expr _tmp7 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp7.v_mut())) {
            auto &[a00] = std::get<typename expr::Val>(_tmp7.v_mut());
            if (a00 <= 0) {
              _stack.emplace_back(_call{_f.a1});
            } else {
              uint64_t n0 = a00 - 1;
              _stack.emplace_back(_after_simplify_in_S{expr::val((n0 + 1))});
              _stack.emplace_back(_call{_f.a1});
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp7.v_mut())) {
            auto &[a00] = std::get<typename expr::Succ>(_tmp7.v_mut());
            _stack.emplace_back(
                _after_simplify_in_Succ_2{expr::succ(crane::shared_child(a00))});
            _stack.emplace_back(_call{_f.a1});
          } else if (std::holds_alternative<typename expr::Add>(_tmp7.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Add>(_tmp7.v_mut());
            _stack.emplace_back(_after_simplify_in_Add_2{
                expr::add(crane::shared_child(a00), crane::shared_child(a10))});
            _stack.emplace_back(_call{_f.a1});
          } else if (std::holds_alternative<typename expr::Mul>(_tmp7.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Mul>(_tmp7.v_mut());
            _stack.emplace_back(_after_simplify_in_Mul{
                expr::mul(crane::shared_child(a00), crane::shared_child(a10))});
            _stack.emplace_back(_call{_f.a1});
          } else {
            auto &[a00, a10, a20] =
                std::get<typename expr::Cond>(_tmp7.v_mut());
            _stack.emplace_back(_after_simplify_in_Cond{
                expr::cond(crane::shared_child(a00), crane::shared_child(a10),
                           crane::shared_child(a20))});
            _stack.emplace_back(_call{_f.a1});
          }
        } else if (std::holds_alternative<_after_simplify_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Add_2>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp4 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp4.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp4.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp4.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp4.v_mut());
            _result =
                expr::add(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp4.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp4.v_mut());
            _result =
                expr::add(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp4.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp4.v_mut());
            _result =
                expr::add(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp4.v_mut());
            _result =
                expr::add(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_Add_3>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Add_3>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp10 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp10.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp10.v_mut());
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
          } else if (
                  std::holds_alternative<typename expr::Succ>(_tmp10.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp10.v_mut());
            _result =
                expr::mul(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp10.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp10.v_mut());
            _result =
                expr::mul(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp10.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp10.v_mut());
            _result =
                expr::mul(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp10.v_mut());
            _result =
                expr::mul(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Cond>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp6 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp6.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp6.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp6.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp6.v_mut());
            _result =
                expr::add(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp6.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp6.v_mut());
            _result =
                expr::add(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp6.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp6.v_mut());
            _result =
                expr::add(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp6.v_mut());
            _result =
                expr::add(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_Cond_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Cond_2>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp12 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp12.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp12.v_mut());
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
          } else if (
                  std::holds_alternative<typename expr::Succ>(_tmp12.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp12.v_mut());
            _result =
                expr::mul(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp12.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp12.v_mut());
            _result =
                expr::mul(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp12.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp12.v_mut());
            _result =
                expr::mul(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp12.v_mut());
            _result =
                expr::mul(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_Cond_3>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Cond_3>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _stack.emplace_back(
              _after_simplify_in_Cond_4{&a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_simplify_in_Cond_4>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Cond_4>(_popped));
          _stack.pop_back();
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_simplify_in_Cond_5{std::move(_f._tmp16),
                                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_simplify_in_Cond_5>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Cond_5>(_popped));
          _stack.pop_back();
          _result = expr::cond(std::move(_f._tmp16), std::move(_f._tmp15),
                               std::move(_result));
        } else if (std::holds_alternative<_after_simplify_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Mul>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp5 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp5.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp5.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp5.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp5.v_mut());
            _result =
                expr::add(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp5.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp5.v_mut());
            _result =
                expr::add(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp5.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp5.v_mut());
            _result =
                expr::add(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp5.v_mut());
            _result =
                expr::add(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Mul_2>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          expr _tmp13 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp13.v_mut())) {
            auto &[a00] = std::get<typename expr::Val>(_tmp13.v_mut());
            if (a00 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a00 - 1;
              _stack.emplace_back(_after_simplify_in_S_2{a00});
              _stack.emplace_back(_call{_f.a1});
            }
          } else if (
                  std::holds_alternative<typename expr::Succ>(_tmp13.v_mut())) {
            auto &[a00] = std::get<typename expr::Succ>(_tmp13.v_mut());
            _stack.emplace_back(
                _after_simplify_in_Succ_3{expr::succ(crane::shared_child(a00))});
            _stack.emplace_back(_call{_f.a1});
          } else if (std::holds_alternative<typename expr::Add>(_tmp13.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Add>(_tmp13.v_mut());
            _stack.emplace_back(_after_simplify_in_Add_3{
                expr::add(crane::shared_child(a00), crane::shared_child(a10))});
            _stack.emplace_back(_call{_f.a1});
          } else if (std::holds_alternative<typename expr::Mul>(_tmp13.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Mul>(_tmp13.v_mut());
            _stack.emplace_back(_after_simplify_in_Mul_3{
                expr::mul(crane::shared_child(a00), crane::shared_child(a10))});
            _stack.emplace_back(_call{_f.a1});
          } else {
            auto &[a00, a10, a20] =
                std::get<typename expr::Cond>(_tmp13.v_mut());
            _stack.emplace_back(_after_simplify_in_Cond_2{
                expr::cond(crane::shared_child(a00), crane::shared_child(a10),
                           crane::shared_child(a20))});
            _stack.emplace_back(_call{_f.a1});
          }
        } else if (std::holds_alternative<_after_simplify_in_Mul_3>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Mul_3>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp11 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp11.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp11.v_mut());
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
          } else if (
                  std::holds_alternative<typename expr::Succ>(_tmp11.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp11.v_mut());
            _result =
                expr::mul(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp11.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp11.v_mut());
            _result =
                expr::mul(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp11.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp11.v_mut());
            _result =
                expr::mul(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp11.v_mut());
            _result =
                expr::mul(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_S>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_S>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp2 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp2.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp2.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n2 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n2 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp2.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp2.v_mut());
            _result =
                expr::add(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp2.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp2.v_mut());
            _result =
                expr::add(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp2.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp2.v_mut());
            _result =
                expr::add(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp2.v_mut());
            _result =
                expr::add(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else if (std::holds_alternative<_after_simplify_in_S_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_S_2>(_popped));
          _stack.pop_back();
          uint64_t a00 = _f.a00;
          expr _tmp8 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp8.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp8.v_mut());
            if (a01 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t n1 = a01 - 1;
              expr s2 = expr::val((n1 + 1));
              if (a00 == UINT64_C(1)) {
                _result = std::move(s2);
              } else {
                _result = expr::mul(expr::val(a00), std::move(s2));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp8.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp8.v_mut());
            expr s2 = expr::succ(crane::shared_child(a01));
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(a00), std::move(s2));
            }
          } else if (std::holds_alternative<typename expr::Add>(_tmp8.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp8.v_mut());
            expr s2 =
                expr::add(crane::shared_child(a01), crane::shared_child(a11));
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(a00), std::move(s2));
            }
          } else if (std::holds_alternative<typename expr::Mul>(_tmp8.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp8.v_mut());
            expr s2 =
                expr::mul(crane::shared_child(a01), crane::shared_child(a11));
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(a00), std::move(s2));
            }
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp8.v_mut());
            expr s2 =
                expr::cond(crane::shared_child(a01), crane::shared_child(a11),
                           crane::shared_child(a21));
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(a00), std::move(s2));
            }
          }
        } else if (std::holds_alternative<_after_simplify_in_Succ>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Succ>(_popped));
          _stack.pop_back();
          _result = expr::succ(std::move(_result));
        } else if (std::holds_alternative<_after_simplify_in_Succ_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_in_Succ_2>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp3 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp3.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp3.v_mut());
            if (a01 <= 0) {
              _result = std::move(s1);
            } else {
              uint64_t n0 = a01 - 1;
              _result = expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_tmp3.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp3.v_mut());
            _result =
                expr::add(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp3.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp3.v_mut());
            _result =
                expr::add(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp3.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp3.v_mut());
            _result =
                expr::add(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp3.v_mut());
            _result =
                expr::add(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        } else {
          auto _f = std::move(std::get<_after_simplify_in_Succ_3>(_popped));
          _stack.pop_back();
          expr s1 = std::move(_f.s1);
          expr _tmp9 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp9.v_mut())) {
            auto &[a01] = std::get<typename expr::Val>(_tmp9.v_mut());
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
          } else if (std::holds_alternative<typename expr::Succ>(_tmp9.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp9.v_mut());
            _result =
                expr::mul(std::move(s1), expr::succ(crane::shared_child(a01)));
          } else if (std::holds_alternative<typename expr::Add>(_tmp9.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp9.v_mut());
            _result =
                expr::mul(std::move(s1), expr::add(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_tmp9.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp9.v_mut());
            _result =
                expr::mul(std::move(s1), expr::mul(crane::shared_child(a01),
                                                   crane::shared_child(a11)));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp9.v_mut());
            _result =
                expr::mul(std::move(s1), expr::cond(crane::shared_child(a01),
                                                    crane::shared_child(a11),
                                                    crane::shared_child(a21)));
          }
        }
      }
      return _result;
    }

    /// size e counts total number of nodes.
    uint64_t size() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of size: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_size_in_Add {
        const expr *a1;
      };

      struct _after_size_in_Add_2 {
        uint64_t _tmp3;
      };

      struct _after_size_in_Cond {
        const expr *a1;
        const expr *a2;
      };

      struct _after_size_in_Cond_2 {
        const expr *a2;
        uint64_t _tmp8;
      };

      struct _after_size_in_Cond_3 {
        uint64_t _tmp8;
        uint64_t _tmp7;
      };

      struct _after_size_in_Mul {
        const expr *a1;
      };

      struct _after_size_in_Mul_2 {
        uint64_t _tmp5;
      };

      struct _after_size_in_Succ {};

      using _frame = std::variant<
          _call, _after_size_in_Add, _after_size_in_Add_2, _after_size_in_Cond,
          _after_size_in_Cond_2, _after_size_in_Cond_3, _after_size_in_Mul,
          _after_size_in_Mul_2, _after_size_in_Succ>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_after_size_in_Succ{});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_size_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_size_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_size_in_Cond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_size_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_size_in_Add_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_size_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Add_2>(_popped));
          _stack.pop_back();
          _result = ((_f._tmp3 + _result) + 1);
        } else if (std::holds_alternative<_after_size_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Cond>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_size_in_Cond_2{&a2, _result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_size_in_Cond_2>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Cond_2>(_popped));
          _stack.pop_back();
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_size_in_Cond_3{_f._tmp8, _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_size_in_Cond_3>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Cond_3>(_popped));
          _stack.pop_back();
          _result = ((_f._tmp8 + (_f._tmp7 + _result)) + 1);
        } else if (std::holds_alternative<_after_size_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_size_in_Mul_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_size_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_size_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = ((_f._tmp5 + _result) + 1);
        } else {
          auto _f = std::move(std::get<_after_size_in_Succ>(_popped));
          _stack.pop_back();
          _result = (_result + 1);
        }
      }
      return _result;
    }

    /// count_vals e counts the number of Val nodes.
    uint64_t count_vals() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of count_vals: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_count_vals_in_Add {
        const expr *a1;
      };

      struct _after_count_vals_in_Add_2 {
        uint64_t _tmp2;
      };

      struct _after_count_vals_in_Cond {
        const expr *a1;
        const expr *a2;
      };

      struct _after_count_vals_in_Cond_2 {
        const expr *a2;
        uint64_t _tmp7;
      };

      struct _after_count_vals_in_Cond_3 {
        uint64_t _tmp7;
        uint64_t _tmp6;
      };

      struct _after_count_vals_in_Mul {
        const expr *a1;
      };

      struct _after_count_vals_in_Mul_2 {
        uint64_t _tmp4;
      };

      using _frame =
          std::variant<_call, _after_count_vals_in_Add,
                       _after_count_vals_in_Add_2, _after_count_vals_in_Cond,
                       _after_count_vals_in_Cond_2, _after_count_vals_in_Cond_3,
                       _after_count_vals_in_Mul, _after_count_vals_in_Mul_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_count_vals_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_count_vals_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_count_vals_in_Cond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_count_vals_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_count_vals_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_count_vals_in_Add_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_count_vals_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_count_vals_in_Add_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp2 + _result;
        } else if (std::holds_alternative<_after_count_vals_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_count_vals_in_Cond>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_count_vals_in_Cond_2{&a2, _result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_count_vals_in_Cond_2>(_popped)) {
          auto _f = std::move(std::get<_after_count_vals_in_Cond_2>(_popped));
          _stack.pop_back();
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_count_vals_in_Cond_3{_f._tmp7, _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_count_vals_in_Cond_3>(_popped)) {
          auto _f = std::move(std::get<_after_count_vals_in_Cond_3>(_popped));
          _stack.pop_back();
          _result = _f._tmp7 + (_f._tmp6 + _result);
        } else if (std::holds_alternative<_after_count_vals_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_count_vals_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_count_vals_in_Mul_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_count_vals_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp4 + _result;
        }
      }
      return _result;
    }

    /// depth e computes expression depth.
    uint64_t depth() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of depth: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_depth_in_Add {
        const expr *a1;
      };

      struct _after_depth_in_Add_2 {
        uint64_t _tmp3;
      };

      struct _after_depth_in_Cond {
        const expr *a1;
        const expr *a2;
      };

      struct _after_depth_in_Cond_2 {
        const expr *a2;
        uint64_t _tmp8;
      };

      struct _after_depth_in_Cond_3 {
        uint64_t _tmp8;
        uint64_t _tmp7;
      };

      struct _after_depth_in_Mul {
        const expr *a1;
      };

      struct _after_depth_in_Mul_2 {
        uint64_t _tmp5;
      };

      struct _after_depth_in_Succ {};

      using _frame = std::variant<
          _call, _after_depth_in_Add, _after_depth_in_Add_2,
          _after_depth_in_Cond, _after_depth_in_Cond_2, _after_depth_in_Cond_3,
          _after_depth_in_Mul, _after_depth_in_Mul_2, _after_depth_in_Succ>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_after_depth_in_Succ{});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_depth_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_depth_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_depth_in_Cond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_depth_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_depth_in_Add_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_depth_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Add_2>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp3, _result) + 1);
        } else if (std::holds_alternative<_after_depth_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Cond>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_depth_in_Cond_2{&a2, _result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_depth_in_Cond_2>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Cond_2>(_popped));
          _stack.pop_back();
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_depth_in_Cond_3{_f._tmp8, _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_depth_in_Cond_3>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Cond_3>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp8, std::max(_f._tmp7, _result)) + 1);
        } else if (std::holds_alternative<_after_depth_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_depth_in_Mul_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_depth_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_depth_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp5, _result) + 1);
        } else {
          auto _f = std::move(std::get<_after_depth_in_Succ>(_popped));
          _stack.pop_back();
          _result = (_result + 1);
        }
      }
      return _result;
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    uint64_t eval() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_eval_in_Add {
        const expr *a1;
      };

      struct _after_eval_in_Add_2 {
        uint64_t _tmp3;
      };

      struct _after_eval_in_Cond {
        const expr *a1;
        const expr *a2;
      };

      struct _after_eval_in_Mul {
        const expr *a1;
      };

      struct _after_eval_in_Mul_2 {
        uint64_t _tmp5;
      };

      struct _after_eval_in_Succ {};

      using _frame = std::variant<
          _call, _after_eval_in_Add, _after_eval_in_Add_2, _after_eval_in_Cond,
          _after_eval_in_Mul, _after_eval_in_Mul_2, _after_eval_in_Succ>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_after_eval_in_Succ{});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_eval_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_eval_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_eval_in_Cond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_in_Add_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Add_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp3 + _result;
        } else if (std::holds_alternative<_after_eval_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Cond>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          if (UINT64_C(0) < _result) {
            _stack.emplace_back(_call{_f.a1});
          } else {
            _stack.emplace_back(_call{_f.a2});
          }
        } else if (std::holds_alternative<_after_eval_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_in_Mul_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp5 * _result;
        } else {
          auto _f = std::move(std::get<_after_eval_in_Succ>(_popped));
          _stack.pop_back();
          _result = (_result + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      return this->template expr_rect<T1>(f, f0, f1, f2, f3);
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_expr_rect_in_Add {
        std::shared_ptr<expr> a0;
        const expr *a1;
      };

      struct _after_expr_rect_in_Add_2 {
        std::shared_ptr<expr> a0;
        const expr *a1;
        T1 _tmp3;
      };

      struct _after_expr_rect_in_Cond {
        std::shared_ptr<expr> a0;
        const expr *a1;
        const expr *a2;
      };

      struct _after_expr_rect_in_Cond_2 {
        std::shared_ptr<expr> a0;
        const expr *a1;
        const expr *a2;
        T1 _tmp8;
      };

      struct _after_expr_rect_in_Cond_3 {
        std::shared_ptr<expr> a0;
        const expr *a1;
        const expr *a2;
        T1 _tmp8;
        T1 _tmp7;
      };

      struct _after_expr_rect_in_Mul {
        std::shared_ptr<expr> a0;
        const expr *a1;
      };

      struct _after_expr_rect_in_Mul_2 {
        std::shared_ptr<expr> a0;
        const expr *a1;
        T1 _tmp5;
      };

      struct _after_expr_rect_in_Succ {
        std::shared_ptr<expr> a0;
      };

      using _frame = std::variant<
          _call, _after_expr_rect_in_Add, _after_expr_rect_in_Add_2,
          _after_expr_rect_in_Cond, _after_expr_rect_in_Cond_2,
          _after_expr_rect_in_Cond_3, _after_expr_rect_in_Mul,
          _after_expr_rect_in_Mul_2, _after_expr_rect_in_Succ>;
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
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Succ{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Add{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Mul{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_expr_rect_in_Cond{a0, crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_expr_rect_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Add>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_expr_rect_in_Add_2{std::move(a0), &a1,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_expr_rect_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Add_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp3), a1, std::move(_result));
        } else if (std::holds_alternative<_after_expr_rect_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Cond>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_expr_rect_in_Cond_2{
              std::move(a0), &a1, &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_expr_rect_in_Cond_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Cond_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _stack.emplace_back(_after_expr_rect_in_Cond_3{
              std::move(a0), &a1, &a2, std::move(_f._tmp8),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_expr_rect_in_Cond_3>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Cond_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          const expr &a2 = *_f.a2;
          _result = f3(*a0, std::move(_f._tmp8), a1, std::move(_f._tmp7), a2,
                       std::move(_result));
        } else if (std::holds_alternative<_after_expr_rect_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Mul>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_expr_rect_in_Mul_2{std::move(a0), &a1,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_expr_rect_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Mul_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _result = f2(*a0, std::move(_f._tmp5), a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_expr_rect_in_Succ>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
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

    static simple_expr plus(crane::shared_child_slot<simple_expr> a0,
                            crane::shared_child_slot<simple_expr> a1) {
      return simple_expr(Plus{a0.take(), a1.take()});
    }

    static simple_expr ifpos(crane::shared_child_slot<simple_expr> a0,
                             crane::shared_child_slot<simple_expr> a1,
                             crane::shared_child_slot<simple_expr> a2) {
      return simple_expr(IfPos{a0.take(), a1.take(), a2.take()});
    }

    // MANIPULATORS
    ~simple_expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Plus>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<IfPos>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
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
    simple_expr(simple_expr &&) = default;
    simple_expr &operator=(simple_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// depth_simple e computes depth of simple expression tree.
    uint64_t depth_simple() const {
      const simple_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of depth_simple: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const simple_expr *_self;
      };

      struct _after_depth_simple_in_IfPos {
        const simple_expr *a1;
        const simple_expr *a2;
      };

      struct _after_depth_simple_in_IfPos_2 {
        const simple_expr *a2;
        uint64_t _tmp5;
      };

      struct _after_depth_simple_in_IfPos_3 {
        uint64_t _tmp5;
        uint64_t _tmp4;
      };

      struct _after_depth_simple_in_Plus {
        const simple_expr *a1;
      };

      struct _after_depth_simple_in_Plus_2 {
        uint64_t _tmp2;
      };

      using _frame = std::variant<
          _call, _after_depth_simple_in_IfPos, _after_depth_simple_in_IfPos_2,
          _after_depth_simple_in_IfPos_3, _after_depth_simple_in_Plus,
          _after_depth_simple_in_Plus_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (
                  std::holds_alternative<typename simple_expr::Plus>(_sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_after_depth_simple_in_Plus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _after_depth_simple_in_IfPos{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_depth_simple_in_IfPos>(_popped)) {
          auto _f = std::move(std::get<_after_depth_simple_in_IfPos>(_popped));
          _stack.pop_back();
          const simple_expr &a1 = *_f.a1;
          const simple_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_depth_simple_in_IfPos_2{&a2, _result});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_depth_simple_in_IfPos_2>(_popped)) {
          auto _f =
              std::move(std::get<_after_depth_simple_in_IfPos_2>(_popped));
          _stack.pop_back();
          const simple_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_depth_simple_in_IfPos_3{_f._tmp5,
                                                             _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (
                std::holds_alternative<_after_depth_simple_in_IfPos_3>(_popped)) {
          auto _f =
              std::move(std::get<_after_depth_simple_in_IfPos_3>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp5, std::max(_f._tmp4, _result)) + 1);
        } else if (std::holds_alternative<_after_depth_simple_in_Plus>(_popped)) {
          auto _f = std::move(std::get<_after_depth_simple_in_Plus>(_popped));
          _stack.pop_back();
          const simple_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_depth_simple_in_Plus_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_depth_simple_in_Plus_2>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp2, _result) + 1);
        }
      }
      return _result;
    }

    /// eval_simple e evaluates simple expression with positive test.
    uint64_t eval_simple() const {
      const simple_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_simple: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const simple_expr *_self;
      };

      struct _after_eval_simple_in_IfPos {
        const simple_expr *a1;
        const simple_expr *a2;
      };

      struct _after_eval_simple_in_Plus {
        const simple_expr *a1;
      };

      struct _after_eval_simple_in_Plus_2 {
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_eval_simple_in_IfPos,
                                  _after_eval_simple_in_Plus,
                                  _after_eval_simple_in_Plus_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (
                  std::holds_alternative<typename simple_expr::Plus>(_sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_after_eval_simple_in_Plus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _after_eval_simple_in_IfPos{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_simple_in_IfPos>(_popped)) {
          auto _f = std::move(std::get<_after_eval_simple_in_IfPos>(_popped));
          _stack.pop_back();
          const simple_expr &a1 = *_f.a1;
          const simple_expr &a2 = *_f.a2;
          if (UINT64_C(0) < _result) {
            _stack.emplace_back(_call{_f.a1});
          } else {
            _stack.emplace_back(_call{_f.a2});
          }
        } else if (std::holds_alternative<_after_eval_simple_in_Plus>(_popped)) {
          auto _f = std::move(std::get<_after_eval_simple_in_Plus>(_popped));
          _stack.pop_back();
          const simple_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_simple_in_Plus_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_eval_simple_in_Plus_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp2 + _result;
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template simple_expr_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of simple_expr_rect:
      // _call frames are pending calls, _after frames resume a caller.
      struct _call {
        const simple_expr *_self;
      };

      struct _after_simple_expr_rect_in_IfPos {
        std::shared_ptr<simple_expr> a0;
        const simple_expr *a1;
        const simple_expr *a2;
      };

      struct _after_simple_expr_rect_in_IfPos_2 {
        std::shared_ptr<simple_expr> a0;
        const simple_expr *a1;
        const simple_expr *a2;
        T1 _tmp5;
      };

      struct _after_simple_expr_rect_in_IfPos_3 {
        std::shared_ptr<simple_expr> a0;
        const simple_expr *a1;
        const simple_expr *a2;
        T1 _tmp5;
        T1 _tmp4;
      };

      struct _after_simple_expr_rect_in_Plus {
        std::shared_ptr<simple_expr> a0;
        const simple_expr *a1;
      };

      struct _after_simple_expr_rect_in_Plus_2 {
        std::shared_ptr<simple_expr> a0;
        const simple_expr *a1;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_simple_expr_rect_in_IfPos,
                                  _after_simple_expr_rect_in_IfPos_2,
                                  _after_simple_expr_rect_in_IfPos_3,
                                  _after_simple_expr_rect_in_Plus,
                                  _after_simple_expr_rect_in_Plus_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (
                  std::holds_alternative<typename simple_expr::Plus>(_sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(
                _after_simple_expr_rect_in_Plus{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_after_simple_expr_rect_in_IfPos{
                a0, crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_simple_expr_rect_in_IfPos>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_simple_expr_rect_in_IfPos>(_popped));
          _stack.pop_back();
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          const simple_expr &a1 = *_f.a1;
          const simple_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_simple_expr_rect_in_IfPos_2{
              std::move(a0), &a1, &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_simple_expr_rect_in_IfPos_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_simple_expr_rect_in_IfPos_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          const simple_expr &a1 = *_f.a1;
          const simple_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_simple_expr_rect_in_IfPos_3{
              std::move(a0), &a1, &a2, std::move(_f._tmp5),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_simple_expr_rect_in_IfPos_3>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_simple_expr_rect_in_IfPos_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          const simple_expr &a1 = *_f.a1;
          const simple_expr &a2 = *_f.a2;
          _result = f1(*a0, std::move(_f._tmp5), a1, std::move(_f._tmp4), a2,
                       std::move(_result));
        } else if (std::holds_alternative<_after_simple_expr_rect_in_Plus>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_simple_expr_rect_in_Plus>(_popped));
          _stack.pop_back();
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          const simple_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_simple_expr_rect_in_Plus_2{
              std::move(a0), &a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_simple_expr_rect_in_Plus_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          const simple_expr &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
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
    T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template shape_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, const uint64_t &>
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

    static cond_expr cplus(crane::shared_child_slot<cond_expr> a0,
                           crane::shared_child_slot<cond_expr> a1) {
      return cond_expr(CPlus{a0.take(), a1.take()});
    }

    static cond_expr ccond(crane::shared_child_slot<cond_expr> a0,
                           crane::shared_child_slot<cond_expr> a1,
                           crane::shared_child_slot<cond_expr> a2) {
      return cond_expr(CCond{a0.take(), a1.take(), a2.take()});
    }

    // MANIPULATORS
    ~cond_expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<CLit>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<CPlus>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<CCond>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
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
    cond_expr(cond_expr &&) = default;
    cond_expr &operator=(cond_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// depth_cond e computes depth of conditional expression tree.
    uint64_t depth_cond() const {
      const cond_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of depth_cond: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const cond_expr *_self;
      };

      struct _after_depth_cond_in_CCond {
        const cond_expr *a1;
        const cond_expr *a2;
      };

      struct _after_depth_cond_in_CCond_2 {
        const cond_expr *a2;
        uint64_t _tmp5;
      };

      struct _after_depth_cond_in_CCond_3 {
        uint64_t _tmp5;
        uint64_t _tmp4;
      };

      struct _after_depth_cond_in_CPlus {
        const cond_expr *a1;
      };

      struct _after_depth_cond_in_CPlus_2 {
        uint64_t _tmp2;
      };

      using _frame = std::variant<
          _call, _after_depth_cond_in_CCond, _after_depth_cond_in_CCond_2,
          _after_depth_cond_in_CCond_3, _after_depth_cond_in_CPlus,
          _after_depth_cond_in_CPlus_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_after_depth_cond_in_CPlus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _after_depth_cond_in_CCond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_depth_cond_in_CCond>(_popped)) {
          auto _f = std::move(std::get<_after_depth_cond_in_CCond>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_depth_cond_in_CCond_2{&a2, _result});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_depth_cond_in_CCond_2>(_popped)) {
          auto _f = std::move(std::get<_after_depth_cond_in_CCond_2>(_popped));
          _stack.pop_back();
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_depth_cond_in_CCond_3{_f._tmp5, _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (
                std::holds_alternative<_after_depth_cond_in_CCond_3>(_popped)) {
          auto _f = std::move(std::get<_after_depth_cond_in_CCond_3>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp5, std::max(_f._tmp4, _result)) + 1);
        } else if (std::holds_alternative<_after_depth_cond_in_CPlus>(_popped)) {
          auto _f = std::move(std::get<_after_depth_cond_in_CPlus>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_depth_cond_in_CPlus_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_depth_cond_in_CPlus_2>(_popped));
          _stack.pop_back();
          _result = (std::max(_f._tmp2, _result) + 1);
        }
      }
      return _result;
    }

    /// eval_cond e evaluates conditional expression.
    uint64_t eval_cond() const {
      const cond_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_cond: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const cond_expr *_self;
      };

      struct _after_eval_cond_in_CCond {
        const cond_expr *a1;
        const cond_expr *a2;
      };

      struct _after_eval_cond_in_CPlus {
        const cond_expr *a1;
      };

      struct _after_eval_cond_in_CPlus_2 {
        uint64_t _tmp2;
      };

      using _frame =
          std::variant<_call, _after_eval_cond_in_CCond,
                       _after_eval_cond_in_CPlus, _after_eval_cond_in_CPlus_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_after_eval_cond_in_CPlus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _after_eval_cond_in_CCond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_cond_in_CCond>(_popped)) {
          auto _f = std::move(std::get<_after_eval_cond_in_CCond>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          if (UINT64_C(0) < _result) {
            _stack.emplace_back(_call{_f.a1});
          } else {
            _stack.emplace_back(_call{_f.a2});
          }
        } else if (std::holds_alternative<_after_eval_cond_in_CPlus>(_popped)) {
          auto _f = std::move(std::get<_after_eval_cond_in_CPlus>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_cond_in_CPlus_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_eval_cond_in_CPlus_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp2 + _result;
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template cond_expr_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of cond_expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const cond_expr *_self;
      };

      struct _after_cond_expr_rect_in_CCond {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        const cond_expr *a2;
      };

      struct _after_cond_expr_rect_in_CCond_2 {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        const cond_expr *a2;
        T1 _tmp5;
      };

      struct _after_cond_expr_rect_in_CCond_3 {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        const cond_expr *a2;
        T1 _tmp5;
        T1 _tmp4;
      };

      struct _after_cond_expr_rect_in_CPlus {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
      };

      struct _after_cond_expr_rect_in_CPlus_2 {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        T1 _tmp2;
      };

      using _frame = std::variant<
          _call, _after_cond_expr_rect_in_CCond,
          _after_cond_expr_rect_in_CCond_2, _after_cond_expr_rect_in_CCond_3,
          _after_cond_expr_rect_in_CPlus, _after_cond_expr_rect_in_CPlus_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(
                _after_cond_expr_rect_in_CPlus{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_after_cond_expr_rect_in_CCond{
                a0, crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_cond_expr_rect_in_CCond>(_popped)) {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_CCond>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_cond_expr_rect_in_CCond_2{
              std::move(a0), &a1, &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_cond_expr_rect_in_CCond_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_CCond_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_cond_expr_rect_in_CCond_3{
              std::move(a0), &a1, &a2, std::move(_f._tmp5),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_cond_expr_rect_in_CCond_3>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_CCond_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _result = f1(*a0, std::move(_f._tmp5), a1, std::move(_f._tmp4), a2,
                       std::move(_result));
        } else if (
                std::holds_alternative<_after_cond_expr_rect_in_CPlus>(_popped)) {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_CPlus>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_cond_expr_rect_in_CPlus_2{
              std::move(a0), &a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_CPlus_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }
  };
};
