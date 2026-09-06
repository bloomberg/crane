#ifndef INCLUDED_GADT_INDEX_ERASURE
#define INCLUDED_GADT_INDEX_ERASURE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a1], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<A> a1;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f(std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
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

    static expr ite(expr a, expr a1, expr a2) {
      return expr(Ite{std::make_shared<expr>(std::move(a)),
                      std::make_shared<expr>(std::move(a1)),
                      std::make_shared<expr>(std::move(a2))});
    }

    static expr pair(expr a, expr b) {
      return expr(Pair{std::make_shared<expr>(std::move(a)),
                       std::make_shared<expr>(std::move(b))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1> static std::any eval(const expr &e) {
    if (std::holds_alternative<typename expr::Lit>(e.v())) {
      const auto &[a0] = std::get<typename expr::Lit>(e.v());
      return a0;
    } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
      const auto &[a0] = std::get<typename expr::Bl>(e.v());
      return a0;
    } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
      const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
      if (std::any_cast<bool>(eval<T1>(*a))) {
        return eval<T1>(*a1);
      } else {
        return eval<T1>(*a2);
      }
    } else {
      const auto &[a0, b0] = std::get<typename expr::Pair>(e.v());
      return std::make_pair(std::any(eval<T1>(*a0)), std::any(eval<T1>(*b0)));
    }
  }

  /// The result is read out of the box at a pair type.
  static inline const uint64_t direct =
      crane_any_cast<std::pair<uint64_t, bool>>(
          eval<std::pair<uint64_t, bool>>(
              expr::pair(expr::ite(expr::bl(true), expr::lit(UINT64_C(3)),
                                   expr::lit(UINT64_C(4))),
                         expr::bl(false))))
          .first;
  /// The evaluator is passed as a function value to map, which instantiates
  /// it at nat while its signature still returns std::any.
  static List<uint64_t> evalAll(const List<expr> &l);
  static inline const uint64_t run =
      (direct +
       evalAll(List<expr>::cons(
                   expr::lit(UINT64_C(1)),
                   List<expr>::cons(expr::lit(UINT64_C(2)), List<expr>::nil())))
           .template fold_right<uint64_t>(
               [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                 return (_x0 + _x1);
               },
               UINT64_C(0)));
};

#endif // INCLUDED_GADT_INDEX_ERASURE
