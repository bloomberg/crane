#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        expr s1;
      };

      /// CraneCont_Add_2: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_2 {
        expr s1;
      };

      /// CraneCont_Cond: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        expr s1;
      };

      /// CraneCont_Cond_1: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond_1 {
        expr s1;
      };

      /// CraneCont_Cond_2: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond_2 {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_3: saves [_tmp16, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_3 {
        expr _tmp16;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_4: saves [_tmp15, _tmp16], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Cond_4 {
        expr _tmp15;
        expr _tmp16;
      };

      /// CraneCont_Mul: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        expr s1;
      };

      /// CraneCont_Mul_1: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_2: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_2 {
        expr s1;
      };

      /// CraneCont_Succ: resumes after recursive call, then processes rest.
      struct CraneCont_Succ {};

      /// CraneCont_Succ_1: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Succ_1 {
        expr s1;
      };

      /// CraneCont_Succ_2: saves [s1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Succ_2 {
        expr s1;
      };

      /// CraneCont_n0: saves [s1], resumes after recursive call, then processes
      /// rest.
      struct CraneCont_n0 {
        expr s1;
      };

      /// CraneCont_px: saves [a00], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_px {
        uint64_t a00;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Add_2, CraneCont_Cond, CraneCont_Cond_1,
                       CraneCont_Cond_2, CraneCont_Cond_3, CraneCont_Cond_4,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Mul_2,
                       CraneCont_Succ, CraneCont_Succ_1, CraneCont_Succ_2,
                       CraneCont_n0, CraneCont_px>;
      expr _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified simplify: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Add_2 -> CraneCont_Cond -> CraneCont_Cond_1 ->
      /// CraneCont_Cond_2 -> CraneCont_Cond_3 -> CraneCont_Cond_4 ->
      /// CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Mul_2 -> CraneCont_Succ
      /// -> CraneCont_Succ_1 -> CraneCont_Succ_2 -> CraneCont_n0 ->
      /// CraneCont_px.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = expr::val(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneCont_Succ{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul_1{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond_2{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          expr _tmp7 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp7.v_mut())) {
            auto &[a00] = std::get<typename expr::Val>(_tmp7.v_mut());
            if (a00 <= 0) {
              _stack.emplace_back(CraneEnter{crane_raw(a1)});
            } else {
              uint64_t n0 = a00 - 1;
              expr s1 = expr::val((n0 + 1));
              _stack.emplace_back(CraneCont_n0{std::move(s1)});
              _stack.emplace_back(CraneEnter{crane_raw(a1)});
            }
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp7.v_mut())) {
            auto &[a00] = std::get<typename expr::Succ>(_tmp7.v_mut());
            expr s1 = expr::succ(*a00);
            _stack.emplace_back(CraneCont_Succ_1{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp7.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Add>(_tmp7.v_mut());
            expr s1 = expr::add(*a00, *a10);
            _stack.emplace_back(CraneCont_Add_1{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp7.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Mul>(_tmp7.v_mut());
            expr s1 = expr::mul(*a00, *a10);
            _stack.emplace_back(CraneCont_Mul{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            auto &[a00, a10, a20] =
                std::get<typename expr::Cond>(_tmp7.v_mut());
            expr s1 = expr::cond(*a00, *a10, *a20);
            _stack.emplace_back(CraneCont_Cond{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp4.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp4.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp4.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp4.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp4.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp4.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp4.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Add_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_2>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp10.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp10.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp10.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp10.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp10.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp10.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp10.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp6.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp6.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp6.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp6.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp6.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp6.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp6.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp12.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp12.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp12.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp12.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp12.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp12.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp12.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_3{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_3>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_3>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_4{std::move(_result), std::move(_f._tmp16)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Cond_4>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_4>(_frame));
          _result = expr::cond(std::move(_f._tmp16), std::move(_f._tmp15),
                               std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp5.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp5.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp5.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp5.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp5.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp5.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp5.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          expr _tmp13 = std::move(_result);
          if (std::holds_alternative<typename expr::Val>(_tmp13.v_mut())) {
            auto &[a00] = std::get<typename expr::Val>(_tmp13.v_mut());
            if (a00 <= 0) {
              _result = expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a00 - 1;
              _stack.emplace_back(CraneCont_px{a00});
              _stack.emplace_back(CraneEnter{crane_raw(a1)});
            }
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp13.v_mut())) {
            auto &[a00] = std::get<typename expr::Succ>(_tmp13.v_mut());
            expr s1 = expr::succ(*a00);
            _stack.emplace_back(CraneCont_Succ_2{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp13.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Add>(_tmp13.v_mut());
            expr s1 = expr::add(*a00, *a10);
            _stack.emplace_back(CraneCont_Add_2{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp13.v_mut())) {
            auto &[a00, a10] = std::get<typename expr::Mul>(_tmp13.v_mut());
            expr s1 = expr::mul(*a00, *a10);
            _stack.emplace_back(CraneCont_Mul_2{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            auto &[a00, a10, a20] =
                std::get<typename expr::Cond>(_tmp13.v_mut());
            expr s1 = expr::cond(*a00, *a10, *a20);
            _stack.emplace_back(CraneCont_Cond_1{std::move(s1)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<CraneCont_Mul_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_2>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp11.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp11.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp11.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp11.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp11.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp11.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp11.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Succ>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Succ>(_frame));
          _result = expr::succ(std::move(_result));
        } else if (std::holds_alternative<CraneCont_Succ_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Succ_1>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp3.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp3.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp3.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp3.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp3.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp3.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp3.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_Succ_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Succ_2>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp9.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp9.v_mut());
            _result = expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp9.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp9.v_mut());
            _result = expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp9.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp9.v_mut());
            _result = expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp9.v_mut());
            _result = expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<CraneCont_n0>(_frame)) {
          auto _f = std::move(std::get<CraneCont_n0>(_frame));
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
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp2.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp2.v_mut());
            _result = expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp2.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp2.v_mut());
            _result = expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp2.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp2.v_mut());
            _result = expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp2.v_mut());
            _result = expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else {
          auto _f = std::move(std::get<CraneCont_px>(_frame));
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
                _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(
                         _tmp8.v_mut())) {
            auto &[a01] = std::get<typename expr::Succ>(_tmp8.v_mut());
            expr s2 = expr::succ(*a01);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          } else if (std::holds_alternative<typename expr::Add>(
                         _tmp8.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Add>(_tmp8.v_mut());
            expr s2 = expr::add(*a01, *a11);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          } else if (std::holds_alternative<typename expr::Mul>(
                         _tmp8.v_mut())) {
            auto &[a01, a11] = std::get<typename expr::Mul>(_tmp8.v_mut());
            expr s2 = expr::mul(*a01, *a11);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          } else {
            auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_tmp8.v_mut());
            expr s2 = expr::cond(*a01, *a11, *a21);
            if (a00 == UINT64_C(1)) {
              _result = std::move(s2);
            } else {
              _result = expr::mul(expr::val(std::move(a00)), std::move(s2));
            }
          }
        }
      }
      return _result;
    }

    /// size e counts total number of nodes.
    uint64_t size() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp3;
      };

      /// CraneCont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp8, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_1 {
        uint64_t _tmp8;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp7, _tmp8], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_2 {
        uint64_t _tmp7;
        uint64_t _tmp8;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        uint64_t _tmp5;
      };

      /// CraneCont_Succ: resumes after recursive call, then processes rest.
      struct CraneCont_Succ {};

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Succ>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified size: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond -> CraneCont_Cond_1 -> CraneCont_Cond_2 ->
      /// CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Succ.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneCont_Succ{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = ((_f._tmp3 + std::move(_result)) + 1);
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_1{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_2{std::move(_result), _f._tmp8});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          _result = ((_f._tmp8 + (_f._tmp7 + std::move(_result))) + 1);
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          _result = ((_f._tmp5 + std::move(_result)) + 1);
        } else {
          auto _f = std::move(std::get<CraneCont_Succ>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    /// count_vals e counts the number of Val nodes.
    uint64_t count_vals() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp7, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_1 {
        uint64_t _tmp7;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp6, _tmp7], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_2 {
        uint64_t _tmp6;
        uint64_t _tmp7;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2,
                       CraneCont_Mul, CraneCont_Mul_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified count_vals: CraneEnter -> CraneCont_Add -> CraneCont_Add_1
      /// -> CraneCont_Cond -> CraneCont_Cond_1 -> CraneCont_Cond_2 ->
      /// CraneCont_Mul -> CraneCont_Mul_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_1{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_2{std::move(_result), _f._tmp7});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          _result = (_f._tmp7 + (_f._tmp6 + std::move(_result)));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          _result = (_f._tmp4 + std::move(_result));
        }
      }
      return _result;
    }

    /// depth e computes expression depth.
    uint64_t depth() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp3;
      };

      /// CraneCont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp8, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_1 {
        uint64_t _tmp8;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp7, _tmp8], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_2 {
        uint64_t _tmp7;
        uint64_t _tmp8;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        uint64_t _tmp5;
      };

      /// CraneCont_Succ: resumes after recursive call, then processes rest.
      struct CraneCont_Succ {};

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Succ>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified depth: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond -> CraneCont_Cond_1 -> CraneCont_Cond_2 ->
      /// CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Succ.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneCont_Succ{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = (std::max(_f._tmp3, std::move(_result)) + 1);
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_1{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_2{std::move(_result), _f._tmp8});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          _result =
              (std::max(_f._tmp8, std::max(_f._tmp7, std::move(_result))) + 1);
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          _result = (std::max(_f._tmp5, std::move(_result)) + 1);
        } else {
          auto _f = std::move(std::get<CraneCont_Succ>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    uint64_t eval() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp3;
      };

      /// CraneCont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        uint64_t _tmp5;
      };

      /// CraneCont_Succ: resumes after recursive call, then processes rest.
      struct CraneCont_Succ {};

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Mul, CraneCont_Mul_1,
                       CraneCont_Succ>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond -> CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Succ.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneCont_Succ{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = (_f._tmp3 + std::move(_result));
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          uint64_t _tmp6 = std::move(_result);
          if (UINT64_C(0) < _tmp6) {
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          _result = (_f._tmp5 * std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Succ>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Add_1 {
        T1 _tmp3;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Cond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp8, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Cond_1 {
        T1 _tmp8;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp7, _tmp8, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Cond_2 {
        T1 _tmp7;
        T1 _tmp8;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Mul: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Mul_1 {
        T1 _tmp5;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Succ: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Succ {
        std::shared_ptr<expr> a0;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Succ>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified expr_rec: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond -> CraneCont_Cond_1 -> CraneCont_Cond_2 ->
      /// CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Succ.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneCont_Succ{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Add_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp3), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_2{std::move(_result), std::move(_f._tmp8),
                               std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _result = f3(*a0, std::move(_f._tmp8), *a1, std::move(_f._tmp7), *a2,
                       std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Mul_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f2(*a0, std::move(_f._tmp5), *a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Succ>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Add_1 {
        T1 _tmp3;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Cond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp8, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Cond_1 {
        T1 _tmp8;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp7, _tmp8, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Cond_2 {
        T1 _tmp7;
        T1 _tmp8;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
        std::shared_ptr<expr> a2;
      };

      /// CraneCont_Mul: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Mul_1 {
        T1 _tmp5;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Succ: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Succ {
        std::shared_ptr<expr> a0;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Succ>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified expr_rect: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond -> CraneCont_Cond_1 -> CraneCont_Cond_2 ->
      /// CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Succ.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(CraneCont_Succ{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Add_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp3), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_2{std::move(_result), std::move(_f._tmp8),
                               std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Cond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          std::shared_ptr<expr> a2 = std::move(_f.a2);
          _result = f3(*a0, std::move(_f._tmp8), *a1, std::move(_f._tmp7), *a2,
                       std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Mul_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f2(*a0, std::move(_f._tmp5), *a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Succ>(_frame));
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
    simple_expr(simple_expr &&) = default;
    simple_expr &operator=(simple_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// depth_simple e computes depth of simple expression tree.
    uint64_t depth_simple() const {
      const simple_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_expr *_self;
      };

      /// CraneCont_IfPos: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_IfPos {
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_IfPos_1: saves [_tmp5, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_IfPos_1 {
        uint64_t _tmp5;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_IfPos_2: saves [_tmp4, _tmp5], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_IfPos_2 {
        uint64_t _tmp4;
        uint64_t _tmp5;
      };

      /// CraneCont_Plus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<simple_expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus_1 {
        uint64_t _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_IfPos, CraneCont_IfPos_1,
                       CraneCont_IfPos_2, CraneCont_Plus, CraneCont_Plus_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified depth_simple: CraneEnter -> CraneCont_IfPos ->
      /// CraneCont_IfPos_1 -> CraneCont_IfPos_2 -> CraneCont_Plus ->
      /// CraneCont_Plus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(CraneCont_IfPos{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_IfPos>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_IfPos_1{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos_1>(_frame));
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_IfPos_2{std::move(_result), _f._tmp5});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_IfPos_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos_2>(_frame));
          _result =
              (std::max(_f._tmp5, std::max(_f._tmp4, std::move(_result))) + 1);
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Plus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          _result = (std::max(_f._tmp2, std::move(_result)) + 1);
        }
      }
      return _result;
    }

    /// eval_simple e evaluates simple expression with positive test.
    uint64_t eval_simple() const {
      const simple_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_expr *_self;
      };

      /// CraneCont_IfPos: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_IfPos {
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_Plus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<simple_expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus_1 {
        uint64_t _tmp2;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_IfPos,
                                      CraneCont_Plus, CraneCont_Plus_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_simple: CraneEnter -> CraneCont_IfPos -> CraneCont_Plus
      /// -> CraneCont_Plus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(CraneCont_IfPos{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_IfPos>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          uint64_t _tmp3 = std::move(_result);
          if (UINT64_C(0) < _tmp3) {
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Plus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_expr *_self;
      };

      /// CraneCont_IfPos: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_IfPos {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_IfPos_1: saves [_tmp5, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_IfPos_1 {
        T1 _tmp5;
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_IfPos_2: saves [_tmp4, _tmp5, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_IfPos_2 {
        T1 _tmp4;
        T1 _tmp5;
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_Plus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Plus_1 {
        T1 _tmp2;
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_IfPos, CraneCont_IfPos_1,
                       CraneCont_IfPos_2, CraneCont_Plus, CraneCont_Plus_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified simple_expr_rec: CraneEnter -> CraneCont_IfPos ->
      /// CraneCont_IfPos_1 -> CraneCont_IfPos_2 -> CraneCont_Plus ->
      /// CraneCont_Plus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(CraneCont_IfPos{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_IfPos>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_IfPos_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_IfPos_2{std::move(_result), std::move(_f._tmp5),
                                std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_IfPos_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos_2>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _result = f1(*a0, std::move(_f._tmp5), *a1, std::move(_f._tmp4), *a2,
                       std::move(_result));
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Plus_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_expr *_self;
      };

      /// CraneCont_IfPos: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_IfPos {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_IfPos_1: saves [_tmp5, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_IfPos_1 {
        T1 _tmp5;
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_IfPos_2: saves [_tmp4, _tmp5, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_IfPos_2 {
        T1 _tmp4;
        T1 _tmp5;
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
        std::shared_ptr<simple_expr> a2;
      };

      /// CraneCont_Plus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Plus_1 {
        T1 _tmp2;
        std::shared_ptr<simple_expr> a0;
        std::shared_ptr<simple_expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_IfPos, CraneCont_IfPos_1,
                       CraneCont_IfPos_2, CraneCont_Plus, CraneCont_Plus_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified simple_expr_rect: CraneEnter -> CraneCont_IfPos ->
      /// CraneCont_IfPos_1 -> CraneCont_IfPos_2 -> CraneCont_Plus ->
      /// CraneCont_Plus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(CraneCont_IfPos{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_IfPos>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_IfPos_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_IfPos_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_IfPos_2{std::move(_result), std::move(_f._tmp5),
                                std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_IfPos_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_IfPos_2>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          std::shared_ptr<simple_expr> a2 = std::move(_f.a2);
          _result = f1(*a0, std::move(_f._tmp5), *a1, std::move(_f._tmp4), *a2,
                       std::move(_result));
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Plus_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          std::shared_ptr<simple_expr> a0 = std::move(_f.a0);
          std::shared_ptr<simple_expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
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
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, const uint64_t &>
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
    cond_expr(cond_expr &&) = default;
    cond_expr &operator=(cond_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// depth_cond e computes depth of conditional expression tree.
    uint64_t depth_cond() const {
      const cond_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_CCond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CCond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CCond_1: saves [_tmp5, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_CCond_1 {
        uint64_t _tmp5;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CCond_2: saves [_tmp4, _tmp5], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_CCond_2 {
        uint64_t _tmp4;
        uint64_t _tmp5;
      };

      /// CraneCont_CPlus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CPlus {
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_CPlus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CPlus_1 {
        uint64_t _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_CCond, CraneCont_CCond_1,
                       CraneCont_CCond_2, CraneCont_CPlus, CraneCont_CPlus_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified depth_cond: CraneEnter -> CraneCont_CCond ->
      /// CraneCont_CCond_1 -> CraneCont_CCond_2 -> CraneCont_CPlus ->
      /// CraneCont_CPlus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(CraneCont_CPlus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(CraneCont_CCond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_CCond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_CCond_1{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_CCond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond_1>(_frame));
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_CCond_2{std::move(_result), _f._tmp5});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_CCond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond_2>(_frame));
          _result =
              (std::max(_f._tmp5, std::max(_f._tmp4, std::move(_result))) + 1);
        } else if (std::holds_alternative<CraneCont_CPlus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_CPlus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_CPlus_1>(_frame));
          _result = (std::max(_f._tmp2, std::move(_result)) + 1);
        }
      }
      return _result;
    }

    /// eval_cond e evaluates conditional expression.
    uint64_t eval_cond() const {
      const cond_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_CCond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CCond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CPlus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CPlus {
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_CPlus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CPlus_1 {
        uint64_t _tmp2;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_CCond,
                                      CraneCont_CPlus, CraneCont_CPlus_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_cond: CraneEnter -> CraneCont_CCond -> CraneCont_CPlus
      /// -> CraneCont_CPlus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(CraneCont_CPlus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(CraneCont_CCond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_CCond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          uint64_t _tmp3 = std::move(_result);
          if (UINT64_C(0) < _tmp3) {
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<CraneCont_CPlus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_CPlus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_CPlus_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_CCond: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_CCond {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CCond_1: saves [_tmp5, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_CCond_1 {
        T1 _tmp5;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CCond_2: saves [_tmp4, _tmp5, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_CCond_2 {
        T1 _tmp4;
        T1 _tmp5;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CPlus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CPlus {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_CPlus_1: saves [_tmp2, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_CPlus_1 {
        T1 _tmp2;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_CCond, CraneCont_CCond_1,
                       CraneCont_CCond_2, CraneCont_CPlus, CraneCont_CPlus_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified cond_expr_rec: CraneEnter -> CraneCont_CCond ->
      /// CraneCont_CCond_1 -> CraneCont_CCond_2 -> CraneCont_CPlus ->
      /// CraneCont_CPlus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(CraneCont_CPlus{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(CraneCont_CCond{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_CCond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_CCond_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_CCond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_CCond_2{std::move(_result), std::move(_f._tmp5),
                                std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_CCond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond_2>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _result = f1(*a0, std::move(_f._tmp5), *a1, std::move(_f._tmp4), *a2,
                       std::move(_result));
        } else if (std::holds_alternative<CraneCont_CPlus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_CPlus_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_CPlus_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_CCond: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_CCond {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CCond_1: saves [_tmp5, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_CCond_1 {
        T1 _tmp5;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CCond_2: saves [_tmp4, _tmp5, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_CCond_2 {
        T1 _tmp4;
        T1 _tmp5;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_CPlus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_CPlus {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_CPlus_1: saves [_tmp2, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_CPlus_1 {
        T1 _tmp2;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_CCond, CraneCont_CCond_1,
                       CraneCont_CCond_2, CraneCont_CPlus, CraneCont_CPlus_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified cond_expr_rect: CraneEnter -> CraneCont_CCond ->
      /// CraneCont_CCond_1 -> CraneCont_CCond_2 -> CraneCont_CPlus ->
      /// CraneCont_CPlus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(CraneCont_CPlus{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(CraneCont_CCond{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_CCond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_CCond_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_CCond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_CCond_2{std::move(_result), std::move(_f._tmp5),
                                std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_CCond_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CCond_2>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _result = f1(*a0, std::move(_f._tmp5), *a1, std::move(_f._tmp4), *a2,
                       std::move(_result));
        } else if (std::holds_alternative<CraneCont_CPlus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_CPlus>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_CPlus_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_CPlus_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
