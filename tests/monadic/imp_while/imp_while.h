#pragma once

#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <crane_fn.h>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstdint>
#include <memory>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

template <typename T1> struct code_const;
template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
enum class STRefs;
struct Expr;
struct Stmt;
template <typename I, typename V, typename A>
concept Code = requires {
  { I::code() } -> std::convertible_to<uint64_t>;
};

struct Nat {};

struct ImpWhile {
  static std::pair<uint64_t, List<uint64_t>> run_factorial(uint64_t k);
  static std::pair<uint64_t, List<uint64_t>> run_fibonacci(uint64_t k);
  static std::pair<uint64_t, List<uint64_t>> run_square(uint64_t k);
  static uint64_t nth(uint64_t n, const List<uint64_t> &l, uint64_t default0);
};

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

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

enum class STRefs { BUILD_STREFS };

template <typename T1> struct code_const {
  constexpr static uint64_t code() { return UINT64_C(0); }
};

struct Expr {
  // TYPES
  struct Num {
    uint64_t n;
  };

  struct Var {
    uint64_t x;
  };

  struct Add {
    std::shared_ptr<Expr> a;
    std::shared_ptr<Expr> b;
  };

  struct Sub {
    std::shared_ptr<Expr> a;
    std::shared_ptr<Expr> b;
  };

  struct Mul {
    std::shared_ptr<Expr> a;
    std::shared_ptr<Expr> b;
  };

  struct Lt {
    std::shared_ptr<Expr> a;
    std::shared_ptr<Expr> b;
  };

  using variant_t = std::variant<Num, Var, Add, Sub, Mul, Lt>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Expr() {}

  explicit Expr(Num _v) : v_(std::move(_v)) {}

  explicit Expr(Var _v) : v_(std::move(_v)) {}

  explicit Expr(Add _v) : v_(std::move(_v)) {}

  explicit Expr(Sub _v) : v_(std::move(_v)) {}

  explicit Expr(Mul _v) : v_(std::move(_v)) {}

  explicit Expr(Lt _v) : v_(std::move(_v)) {}

  static Expr num(uint64_t n) { return Expr(Num{n}); }

  static Expr var(uint64_t x) { return Expr(Var{x}); }

  static Expr add(crane::shared_child_slot<Expr> a,
                  crane::shared_child_slot<Expr> b) {
    return Expr(Add{a.take(), b.take()});
  }

  static Expr sub(crane::shared_child_slot<Expr> a,
                  crane::shared_child_slot<Expr> b) {
    return Expr(Sub{a.take(), b.take()});
  }

  static Expr mul(crane::shared_child_slot<Expr> a,
                  crane::shared_child_slot<Expr> b) {
    return Expr(Mul{a.take(), b.take()});
  }

  static Expr lt(crane::shared_child_slot<Expr> a,
                 crane::shared_child_slot<Expr> b) {
    return Expr(Lt{a.take(), b.take()});
  }

  // MANIPULATORS
  ~Expr() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
    if (auto *_alt = std::get_if<Sub>(&v_mut())) {
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
    if (auto *_alt = std::get_if<Lt>(&v_mut())) {
      if (!((_alt->a && _alt->a.use_count() == 1) ||
            (_alt->b && _alt->b.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Expr>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Add>(&_v)) {
        if (_alt->a && _alt->a.use_count() == 1) {
          _stack.push_back(std::move(_alt->a));
        }
        if (_alt->b && _alt->b.use_count() == 1) {
          _stack.push_back(std::move(_alt->b));
        }
      }
      if (auto *_alt = std::get_if<Sub>(&_v)) {
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
      if (auto *_alt = std::get_if<Lt>(&_v)) {
        if (_alt->a && _alt->a.use_count() == 1) {
          _stack.push_back(std::move(_alt->a));
        }
        if (_alt->b && _alt->b.use_count() == 1) {
          _stack.push_back(std::move(_alt->b));
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

  Expr(const Expr &) = default;
  Expr &operator=(const Expr &) = default;
  Expr(Expr &&) = default;
  Expr &operator=(Expr &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Stmt {
  // TYPES
  struct Skip {};

  struct Assign {
    uint64_t x;
    Expr e;
  };

  struct Seq {
    std::shared_ptr<Stmt> s1;
    std::shared_ptr<Stmt> s2;
  };

  struct If {
    Expr c;
    std::shared_ptr<Stmt> s1;
    std::shared_ptr<Stmt> s2;
  };

  struct While {
    Expr c;
    std::shared_ptr<Stmt> body;
  };

  using variant_t = std::variant<Skip, Assign, Seq, If, While>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Stmt() {}

  explicit Stmt(Skip _v) : v_(_v) {}

  explicit Stmt(Assign _v) : v_(std::move(_v)) {}

  explicit Stmt(Seq _v) : v_(std::move(_v)) {}

  explicit Stmt(If _v) : v_(std::move(_v)) {}

  explicit Stmt(While _v) : v_(std::move(_v)) {}

  static Stmt skip() { return Stmt(Skip{}); }

  static Stmt assign(uint64_t x, Expr e) {
    return Stmt(Assign{x, std::move(e)});
  }

  static Stmt seq(crane::shared_child_slot<Stmt> s1,
                  crane::shared_child_slot<Stmt> s2) {
    return Stmt(Seq{s1.take(), s2.take()});
  }

  static Stmt If_(Expr c, crane::shared_child_slot<Stmt> s1,
                  crane::shared_child_slot<Stmt> s2) {
    return Stmt(If{std::move(c), s1.take(), s2.take()});
  }

  static Stmt While_(Expr c, crane::shared_child_slot<Stmt> body) {
    return Stmt(While{std::move(c), body.take()});
  }

  // MANIPULATORS
  ~Stmt() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    if (std::holds_alternative<Skip>(v_mut())) {
      return;
    }
    if (std::holds_alternative<Assign>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<Seq>(&v_mut())) {
      if (!((_alt->s1 && _alt->s1.use_count() == 1) ||
            (_alt->s2 && _alt->s2.use_count() == 1))) {
        return;
      }
    }
    if (auto *_alt = std::get_if<If>(&v_mut())) {
      if (!((_alt->s1 && _alt->s1.use_count() == 1) ||
            (_alt->s2 && _alt->s2.use_count() == 1))) {
        return;
      }
    }
    if (auto *_alt = std::get_if<While>(&v_mut())) {
      if (!(_alt->body && _alt->body.use_count() == 1)) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Stmt>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Seq>(&_v)) {
        if (_alt->s1 && _alt->s1.use_count() == 1) {
          _stack.push_back(std::move(_alt->s1));
        }
        if (_alt->s2 && _alt->s2.use_count() == 1) {
          _stack.push_back(std::move(_alt->s2));
        }
      }
      if (auto *_alt = std::get_if<If>(&_v)) {
        if (_alt->s1 && _alt->s1.use_count() == 1) {
          _stack.push_back(std::move(_alt->s1));
        }
        if (_alt->s2 && _alt->s2.use_count() == 1) {
          _stack.push_back(std::move(_alt->s2));
        }
      }
      if (auto *_alt = std::get_if<While>(&_v)) {
        if (_alt->body && _alt->body.use_count() == 1) {
          _stack.push_back(std::move(_alt->body));
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

  Stmt(const Stmt &) = default;
  Stmt &operator=(const Stmt &) = default;
  Stmt(Stmt &&) = default;
  Stmt &operator=(Stmt &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// The value of e, the variables read from vars.
uint64_t eval(STRefs r, std::span<const uint64_t> vars, const Expr &e);
/// One statement: its substatements are run by call.
uint64_t exec_body(STRefs r, std::span<uint64_t> vars, const Stmt &s);
uint64_t exec(STRefs r,
              const std::shared_ptr<crane::array_storage<uint64_t>> &vars,
              const Stmt &s);
/// Runs s on n variables, all 0: the steps it took and the final
/// variables.
std::pair<uint64_t, List<uint64_t>> run(STRefs r, uint64_t n, const Stmt &s);
/// x1 := k!, counting x0 down from k.
Stmt factorial(uint64_t k);
/// x1 := fib k, counting x0 down from k with (x1, x2) := (x2, x1 + x2).
Stmt fibonacci(uint64_t k);
/// A nested loop: x2 := k * k, one increment at a time.
Stmt square(uint64_t k);
