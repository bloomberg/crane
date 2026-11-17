#ifndef INCLUDED_GADT_INDEX_ERASURE
#define INCLUDED_GADT_INDEX_ERASURE

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
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of fold_right: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_fold_right_in_Cons {
      A a1;
    };

    using _frame = std::variant<_call, _after_fold_right_in_Cons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_fold_right_in_Cons{a1});
          _stack.emplace_back(_call{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_after_fold_right_in_Cons>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct GadtIndexErasure {
  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Bl {
      bool a0;
    };

    struct Ite {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    struct Pair {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> b;
    };

    using variant_t = std::variant<Lit, Bl, Ite, Pair>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Bl _v) : v_(std::move(_v)) {}

    explicit expr(Ite _v) : v_(std::move(_v)) {}

    explicit expr(Pair _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr bl(bool a0) { return expr(Bl{a0}); }

    static expr ite(crane::shared_child_slot<expr> a,
                    crane::shared_child_slot<expr> a1,
                    crane::shared_child_slot<expr> a2) {
      return expr(Ite{a.take(), a1.take(), a2.take()});
    }

    static expr pair(crane::shared_child_slot<expr> a,
                     crane::shared_child_slot<expr> b) {
      return expr(Pair{a.take(), b.take()});
    }

    // MANIPULATORS
    ~expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (std::holds_alternative<Bl>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Ite>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Pair>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->b && _alt->b.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Ite>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
        if (auto *_alt = std::get_if<Pair>(&_v)) {
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

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1 = void> static crane::obj eval(const expr &e) {
    if (std::holds_alternative<typename expr::Lit>(e.v())) {
      const auto &[a0] = std::get<typename expr::Lit>(e.v());
      return a0;
    } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
      const auto &[a0] = std::get<typename expr::Bl>(e.v());
      return a0;
    } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
      const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
      if (crane::any_cast<bool>(eval<bool>(*a))) {
        return eval<crane::obj>(*a1);
      } else {
        return eval<crane::obj>(*a2);
      }
    } else {
      const auto &[a0, b0] = std::get<typename expr::Pair>(e.v());
      return std::make_pair(crane::obj(eval<crane::obj>(*a0)),
                            crane::obj(eval<crane::obj>(*b0)));
    }
  }

  /// The result is read out of the box at a pair type.
  static inline const uint64_t direct =
      crane_any_cast<std::pair<uint64_t, bool>>(
          eval<std::pair<uint64_t, bool>>(expr::pair(expr::ite(
              expr::bl(true), expr::lit(UINT64_C(3)), expr::lit(UINT64_C(4))),
                                                     expr::bl(false))))
          .first;
  /// The evaluator is passed as a function value to map, which instantiates
  /// it at nat while its signature still returns std::any.
  static List<uint64_t> evalAll(const List<expr> &l);
  static inline const uint64_t run =
      (direct +
       evalAll(List<expr>::cons(
           expr::lit(UINT64_C(1)),
           List<expr>::cons(expr::lit(UINT64_C(2)),
                            List<expr>::nil())))
           .template fold_right<uint64_t>(
           [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
           UINT64_C(0)));
};

#endif // INCLUDED_GADT_INDEX_ERASURE
