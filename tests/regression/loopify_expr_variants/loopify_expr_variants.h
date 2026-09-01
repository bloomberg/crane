#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
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

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, uint64_t n);
};

struct LoopifyExprVariants {
  struct cond_expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Add {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
    };

    struct Cond {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
      std::shared_ptr<cond_expr> a2;
    };

    using variant_t = std::variant<Lit, Add, Cond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(Lit _v) : v_(std::move(_v)) {}

    explicit cond_expr(Add _v) : v_(std::move(_v)) {}

    explicit cond_expr(Cond _v) : v_(std::move(_v)) {}

    static cond_expr lit(uint64_t a0) { return cond_expr(Lit{a0}); }

    static cond_expr add(cond_expr a0, cond_expr a1) {
      return cond_expr(Add{std::make_shared<cond_expr>(std::move(a0)),
                           std::make_shared<cond_expr>(std::move(a1))});
    }

    static cond_expr cond(cond_expr a0, cond_expr a1, cond_expr a2) {
      return cond_expr(Cond{std::make_shared<cond_expr>(std::move(a0)),
                            std::make_shared<cond_expr>(std::move(a1)),
                            std::make_shared<cond_expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~cond_expr() {
      crane::small_vector<std::shared_ptr<cond_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Cond>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
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

    uint64_t size_cond() const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_Add: saves [a0, _s1], dispatches next recursive call.
      struct _After_Add {
        cond_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _After_Cond: saves [a1, a0, _s2], dispatches next recursive call.
      struct _After_Cond {
        const cond_expr *a1;
        const cond_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s2;
      };

      /// _After_Cond_1: saves [_result, a0, _s2], dispatches next recursive
      /// call.
      struct _After_Cond_1 {
        uint64_t _result;
        const cond_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s2;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        uint64_t _result_0;
        uint64_t _result_1;
        std::decay_t<decltype(UINT64_C(1))> _s2;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _Combine_Add, _Combine_Cond>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified size_cond: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _Combine_Add -> _Combine_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _After_Cond{crane_raw(a1), crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{std::move(_result), _f.a0, _f._s2});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(
              _Combine_Cond{_f._result, std::move(_result), _f._s2});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result =
              (((_f._s2 + std::move(_result)) + _f._result_1) + _f._result_0);
        }
      }
      return _result;
    }

    uint64_t eval_cond() const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_Add: saves [a0], dispatches next recursive call.
      struct _After_Add {
        cond_expr *a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        uint64_t _result;
      };

      /// _Cont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      using _Frame = std::variant<_Enter, _After_Add, _Combine_Add, _Cont_Cond>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_cond: _Enter -> _After_Add -> _Combine_Add ->
      /// _Cont_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(_Cont_Cond{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Cont_Cond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          uint64_t _rc1 = std::move(_result);
          if (UINT64_C(0) < _rc1) {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
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

      /// _After_Add: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Add {
        cond_expr *a0_0;
        cond_expr a1;
        cond_expr a0_1;
      };

      /// _After_Cond: saves [a1_0, a0_0, a2, a1_1, a0_1], dispatches next
      /// recursive call.
      struct _After_Cond {
        const cond_expr *a1_0;
        const cond_expr *a0_0;
        cond_expr a2;
        cond_expr a1_1;
        cond_expr a0_1;
      };

      /// _After_Cond_1: saves [_result, a0_0, a2, a1, a0_1], dispatches next
      /// recursive call.
      struct _After_Cond_1 {
        std::decay_t<T1> _result;
        const cond_expr *a0_0;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0_1;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        std::decay_t<T1> _result;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _Combine_Add, _Combine_Cond>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rec: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _Combine_Add -> _Combine_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _After_Cond{crane_raw(a1), crane_raw(a0), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(
              _After_Cond_1{std::move(_result), _f.a0_0, std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{
              std::move(_f._result), std::move(_result), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_1), std::move(_f.a2),
                       std::move(_f._result_0));
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

      /// _After_Add: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Add {
        cond_expr *a0_0;
        cond_expr a1;
        cond_expr a0_1;
      };

      /// _After_Cond: saves [a1_0, a0_0, a2, a1_1, a0_1], dispatches next
      /// recursive call.
      struct _After_Cond {
        const cond_expr *a1_0;
        const cond_expr *a0_0;
        cond_expr a2;
        cond_expr a1_1;
        cond_expr a0_1;
      };

      /// _After_Cond_1: saves [_result, a0_0, a2, a1, a0_1], dispatches next
      /// recursive call.
      struct _After_Cond_1 {
        std::decay_t<T1> _result;
        const cond_expr *a0_0;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0_1;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        std::decay_t<T1> _result;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _Combine_Add, _Combine_Cond>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rect: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _Combine_Add -> _Combine_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _After_Cond{crane_raw(a1), crane_raw(a0), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(
              _After_Cond_1{std::move(_result), _f.a0_0, std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{
              std::move(_f._result), std::move(_result), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_1), std::move(_f.a2),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }
  };

  struct arith_expr {
    // TYPES
    struct ANum {
      uint64_t a0;
    };

    struct AAdd {
      std::shared_ptr<arith_expr> a0;
      std::shared_ptr<arith_expr> a1;
    };

    struct AMul {
      std::shared_ptr<arith_expr> a0;
      std::shared_ptr<arith_expr> a1;
    };

    struct ADiv {
      std::shared_ptr<arith_expr> a0;
      std::shared_ptr<arith_expr> a1;
    };

    using variant_t = std::variant<ANum, AAdd, AMul, ADiv>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    arith_expr() {}

    explicit arith_expr(ANum _v) : v_(std::move(_v)) {}

    explicit arith_expr(AAdd _v) : v_(std::move(_v)) {}

    explicit arith_expr(AMul _v) : v_(std::move(_v)) {}

    explicit arith_expr(ADiv _v) : v_(std::move(_v)) {}

    static arith_expr anum(uint64_t a0) { return arith_expr(ANum{a0}); }

    static arith_expr aadd(arith_expr a0, arith_expr a1) {
      return arith_expr(AAdd{std::make_shared<arith_expr>(std::move(a0)),
                             std::make_shared<arith_expr>(std::move(a1))});
    }

    static arith_expr amul(arith_expr a0, arith_expr a1) {
      return arith_expr(AMul{std::make_shared<arith_expr>(std::move(a0)),
                             std::make_shared<arith_expr>(std::move(a1))});
    }

    static arith_expr adiv(arith_expr a0, arith_expr a1) {
      return arith_expr(ADiv{std::make_shared<arith_expr>(std::move(a0)),
                             std::make_shared<arith_expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~arith_expr() {
      crane::small_vector<std::shared_ptr<arith_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<AAdd>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<AMul>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<ADiv>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    arith_expr(const arith_expr &) = default;
    arith_expr &operator=(const arith_expr &) = default;
    arith_expr(arith_expr &&) noexcept = default;
    arith_expr &operator=(arith_expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t count_ops() const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [a0, _s1], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _After_ADiv: saves [a0, _s1], dispatches next recursive call.
      struct _After_ADiv {
        arith_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _After_AMul: saves [a0, _s1], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_ADiv: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ADiv {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      using _Frame = std::variant<_Enter, _After_AAdd, _After_ADiv, _After_AMul,
                                  _Combine_AAdd, _Combine_ADiv, _Combine_AMul>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified count_ops: _Enter -> _After_AAdd -> _After_ADiv ->
      /// _After_AMul -> _Combine_AAdd -> _Combine_ADiv -> _Combine_AMul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_After_ADiv{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(_Combine_AAdd{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_ADiv>(_frame)) {
          auto _f = std::move(std::get<_After_ADiv>(_frame));
          _stack.emplace_back(_Combine_ADiv{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(_Combine_AMul{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else if (std::holds_alternative<_Combine_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Combine_ADiv>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        }
      }
      return _result;
    }

    uint64_t eval_arith() const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [a0], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *a0;
      };

      /// _After_AMul: saves [a0], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *a0;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        uint64_t _result;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        uint64_t _result;
      };

      /// _Cont_ADiv: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct _Cont_ADiv {
        std::shared_ptr<arith_expr> a0;
      };

      /// _Resume_n: saves [n], resumes after recursive call with _result.
      struct _Resume_n {
        std::decay_t<decltype((std::declval<uint64_t &>() + 1))> n;
      };

      using _Frame =
          std::variant<_Enter, _After_AAdd, _After_AMul, _Combine_AAdd,
                       _Combine_AMul, _Cont_ADiv, _Resume_n>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_arith: _Enter -> _After_AAdd -> _After_AMul ->
      /// _Combine_AAdd -> _Combine_AMul -> _Cont_ADiv -> _Resume_n.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_Cont_ADiv{a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(_Combine_AAdd{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(_Combine_AMul{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        } else if (std::holds_alternative<_Combine_AMul>(_frame)) {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = (std::move(_result) * std::move(_f._result));
        } else if (std::holds_alternative<_Cont_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Cont_ADiv>(_frame));
          std::shared_ptr<arith_expr> a0 = std::move(_f.a0);
          auto _cs = std::move(_result);
          if (_cs <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t n = _cs - 1;
            _stack.emplace_back(_Resume_n{(n + 1)});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_n>(_frame));
          _result = (_f.n ? std::move(_result) / _f.n : 0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &>
    T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *a2_0;
        arith_expr a3;
        arith_expr a2_1;
      };

      /// _After_ADiv: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_ADiv {
        arith_expr *a2_0;
        arith_expr a3;
        arith_expr a2_1;
      };

      /// _After_AMul: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *a2_0;
        arith_expr a3;
        arith_expr a2_1;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        std::decay_t<T1> _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_ADiv: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ADiv {
        std::decay_t<T1> _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        std::decay_t<T1> _result;
        arith_expr a3;
        arith_expr a2;
      };

      using _Frame = std::variant<_Enter, _After_AAdd, _After_ADiv, _After_AMul,
                                  _Combine_AAdd, _Combine_ADiv, _Combine_AMul>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified arith_expr_rec: _Enter -> _After_AAdd -> _After_ADiv ->
      /// _After_AMul -> _Combine_AAdd -> _Combine_ADiv -> _Combine_AMul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          } else {
            const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_After_ADiv{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(_Combine_AAdd{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_ADiv>(_frame)) {
          auto _f = std::move(std::get<_After_ADiv>(_frame));
          _stack.emplace_back(_Combine_ADiv{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(_Combine_AMul{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = f0(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        } else if (std::holds_alternative<_Combine_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Combine_ADiv>(_frame));
          _result = f2(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = f1(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &>
    T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *a2_0;
        arith_expr a3;
        arith_expr a2_1;
      };

      /// _After_ADiv: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_ADiv {
        arith_expr *a2_0;
        arith_expr a3;
        arith_expr a2_1;
      };

      /// _After_AMul: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *a2_0;
        arith_expr a3;
        arith_expr a2_1;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        std::decay_t<T1> _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_ADiv: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ADiv {
        std::decay_t<T1> _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        std::decay_t<T1> _result;
        arith_expr a3;
        arith_expr a2;
      };

      using _Frame = std::variant<_Enter, _After_AAdd, _After_ADiv, _After_AMul,
                                  _Combine_AAdd, _Combine_ADiv, _Combine_AMul>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified arith_expr_rect: _Enter -> _After_AAdd -> _After_ADiv ->
      /// _After_AMul -> _Combine_AAdd -> _Combine_ADiv -> _Combine_AMul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          } else {
            const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_After_ADiv{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(_Combine_AAdd{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_ADiv>(_frame)) {
          auto _f = std::move(std::get<_After_ADiv>(_frame));
          _stack.emplace_back(_Combine_ADiv{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(_Combine_AMul{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = f0(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        } else if (std::holds_alternative<_Combine_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Combine_ADiv>(_frame));
          _result = f2(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = f1(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };

  struct bool_expr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<bool_expr> a0;
      std::shared_ptr<bool_expr> a1;
    };

    struct BOr {
      std::shared_ptr<bool_expr> a0;
      std::shared_ptr<bool_expr> a1;
    };

    struct BNot {
      std::shared_ptr<bool_expr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bool_expr() {}

    explicit bool_expr(BTrue _v) : v_(_v) {}

    explicit bool_expr(BFalse _v) : v_(_v) {}

    explicit bool_expr(BAnd _v) : v_(std::move(_v)) {}

    explicit bool_expr(BOr _v) : v_(std::move(_v)) {}

    explicit bool_expr(BNot _v) : v_(std::move(_v)) {}

    static bool_expr btrue() { return bool_expr(BTrue{}); }

    static bool_expr bfalse() { return bool_expr(BFalse{}); }

    static bool_expr band(bool_expr a0, bool_expr a1) {
      return bool_expr(BAnd{std::make_shared<bool_expr>(std::move(a0)),
                            std::make_shared<bool_expr>(std::move(a1))});
    }

    static bool_expr bor(bool_expr a0, bool_expr a1) {
      return bool_expr(BOr{std::make_shared<bool_expr>(std::move(a0)),
                           std::make_shared<bool_expr>(std::move(a1))});
    }

    static bool_expr bnot(bool_expr a0) {
      return bool_expr(BNot{std::make_shared<bool_expr>(std::move(a0))});
    }

    // MANIPULATORS
    ~bool_expr() {
      crane::small_vector<std::shared_ptr<bool_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BAnd>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BOr>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BNot>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
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

    bool_expr(const bool_expr &) = default;
    bool_expr &operator=(const bool_expr &) = default;
    bool_expr(bool_expr &&) noexcept = default;
    bool_expr &operator=(bool_expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool_expr simplify_bool() const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _Cont_BAnd: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BAnd {
        std::shared_ptr<bool_expr> a1;
      };

      /// _Cont_BAnd_1: saves [a_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BAnd_1 {
        bool_expr a_;
      };

      /// _Cont_BAnd_2: saves [a_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BAnd_2 {
        bool_expr a_;
      };

      /// _Cont_BFalse: resumes after recursive call, then processes rest.
      struct _Cont_BFalse {};

      /// _Cont_BNot: saves [a_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BNot {
        bool_expr a_;
      };

      /// _Cont_BNot_1: saves [a_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BNot_1 {
        bool_expr a_;
      };

      /// _Cont_BNot_2: resumes after recursive call, then processes rest.
      struct _Cont_BNot_2 {};

      /// _Cont_BOr: saves [a_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BOr {
        bool_expr a_;
      };

      /// _Cont_BOr_1: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BOr_1 {
        std::shared_ptr<bool_expr> a1;
      };

      /// _Cont_BOr_2: saves [a_], resumes after recursive call, then processes
      /// rest.
      struct _Cont_BOr_2 {
        bool_expr a_;
      };

      /// _Cont_BTrue: resumes after recursive call, then processes rest.
      struct _Cont_BTrue {};

      using _Frame =
          std::variant<_Enter, _Cont_BAnd, _Cont_BAnd_1, _Cont_BAnd_2,
                       _Cont_BFalse, _Cont_BNot, _Cont_BNot_1, _Cont_BNot_2,
                       _Cont_BOr, _Cont_BOr_1, _Cont_BOr_2, _Cont_BTrue>;
      bool_expr _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simplify_bool: _Enter -> _Cont_BAnd -> _Cont_BAnd_1 ->
      /// _Cont_BAnd_2 -> _Cont_BFalse -> _Cont_BNot -> _Cont_BNot_1 ->
      /// _Cont_BNot_2 -> _Cont_BOr -> _Cont_BOr_1 -> _Cont_BOr_2 ->
      /// _Cont_BTrue.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_Cont_BAnd{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_Cont_BOr_1{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Cont_BNot_2{});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Cont_BAnd>(_frame));
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          bool_expr _rc1 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc1.v())) {
            _stack.emplace_back(_Cont_BTrue{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc1.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc1.v())) {
            const auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_rc1.v());
            bool_expr a_ = bool_expr::band(*a00, *a10);
            _stack.emplace_back(_Cont_BAnd_1{std::move(a_)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc1.v())) {
            const auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_rc1.v());
            bool_expr a_ = bool_expr::bor(*a00, *a10);
            _stack.emplace_back(_Cont_BOr{std::move(a_)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a00] = std::get<typename bool_expr::BNot>(_rc1.v());
            bool_expr a_ = bool_expr::bnot(*a00);
            _stack.emplace_back(_Cont_BNot{std::move(a_)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_Cont_BAnd_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_BAnd_1>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _rc3 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc3.v())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc3.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc3.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc3.v());
            _result =
                bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc3.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc3.v());
            _result =
                bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc3.v());
            _result = bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<_Cont_BAnd_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_BAnd_2>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _rc8 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc8.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc8.v())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc8.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc8.v());
            _result =
                bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc8.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc8.v());
            _result = bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc8.v());
            _result = bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<_Cont_BFalse>(_frame)) {
          auto _f = std::move(std::get<_Cont_BFalse>(_frame));
          bool_expr _rc7 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc7.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc7.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc7.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc7.v());
            _result = bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc7.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc7.v());
            _result = bool_expr::bor(*a01, *a11);
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc7.v());
            _result = bool_expr::bnot(*a01);
          }
        } else if (std::holds_alternative<_Cont_BNot>(_frame)) {
          auto _f = std::move(std::get<_Cont_BNot>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _rc5 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc5.v())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc5.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc5.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc5.v());
            _result =
                bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc5.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc5.v());
            _result =
                bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc5.v());
            _result = bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<_Cont_BNot_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_BNot_1>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _rc10 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc10.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc10.v())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc10.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc10.v());
            _result =
                bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc10.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc10.v());
            _result = bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc10.v());
            _result = bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<_Cont_BNot_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_BNot_2>(_frame));
          bool_expr _rc11 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc11.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc11.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc11.v())) {
            const auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_rc11.v());
            _result = bool_expr::bnot(bool_expr::band(*a00, *a10));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc11.v())) {
            const auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_rc11.v());
            _result = bool_expr::bnot(bool_expr::bor(*a00, *a10));
          } else {
            const auto &[a00] = std::get<typename bool_expr::BNot>(_rc11.v());
            _result = bool_expr::bnot(bool_expr::bnot(*a00));
          }
        } else if (std::holds_alternative<_Cont_BOr>(_frame)) {
          auto _f = std::move(std::get<_Cont_BOr>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _rc4 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc4.v())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc4.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc4.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc4.v());
            _result =
                bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc4.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc4.v());
            _result =
                bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc4.v());
            _result = bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<_Cont_BOr_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_BOr_1>(_frame));
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          bool_expr _rc6 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc6.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc6.v())) {
            _stack.emplace_back(_Cont_BFalse{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc6.v())) {
            const auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_rc6.v());
            bool_expr a_ = bool_expr::band(*a00, *a10);
            _stack.emplace_back(_Cont_BAnd_2{std::move(a_)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc6.v())) {
            const auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_rc6.v());
            bool_expr a_ = bool_expr::bor(*a00, *a10);
            _stack.emplace_back(_Cont_BOr_2{std::move(a_)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a00] = std::get<typename bool_expr::BNot>(_rc6.v());
            bool_expr a_ = bool_expr::bnot(*a00);
            _stack.emplace_back(_Cont_BNot_1{std::move(a_)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_Cont_BOr_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_BOr_2>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _rc9 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc9.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc9.v())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc9.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc9.v());
            _result =
                bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc9.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc9.v());
            _result = bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc9.v());
            _result = bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else {
          auto _f = std::move(std::get<_Cont_BTrue>(_frame));
          bool_expr _rc2 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_rc2.v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _rc2.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _rc2.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_rc2.v());
            _result = bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _rc2.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_rc2.v());
            _result = bool_expr::bor(*a01, *a11);
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_rc2.v());
            _result = bool_expr::bnot(*a01);
          }
        }
      }
      return _result;
    }

    bool eval_bool() const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _After_BAnd: saves [a0], dispatches next recursive call.
      struct _After_BAnd {
        bool_expr *a0;
      };

      /// _After_BOr: saves [a0], dispatches next recursive call.
      struct _After_BOr {
        bool_expr *a0;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        bool _result;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        bool _result;
      };

      /// _Resume_BNot: resumes after recursive call with _result.
      struct _Resume_BNot {};

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      bool _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_bool: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = true;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = (std::move(_result) && std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = (std::move(_result) || std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = !(std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F4 &, bool_expr &, T1 &>
    T1 bool_expr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _After_BAnd: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BAnd {
        bool_expr *a0_0;
        bool_expr a1;
        bool_expr a0_1;
      };

      /// _After_BOr: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BOr {
        bool_expr *a0_0;
        bool_expr a1;
        bool_expr a0_1;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        std::decay_t<T1> _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        std::decay_t<T1> _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Resume_BNot: saves [a0], resumes after recursive call with _result.
      struct _Resume_BNot {
        bool_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_expr_rec: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{*a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = f2(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = f3(std::move(_f.a0), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F4 &, bool_expr &, T1 &>
    T1 bool_expr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _After_BAnd: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BAnd {
        bool_expr *a0_0;
        bool_expr a1;
        bool_expr a0_1;
      };

      /// _After_BOr: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BOr {
        bool_expr *a0_0;
        bool_expr a1;
        bool_expr a0_1;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        std::decay_t<T1> _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        std::decay_t<T1> _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Resume_BNot: saves [a0], resumes after recursive call with _result.
      struct _Resume_BNot {
        bool_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_expr_rect: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{*a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = f2(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = f3(std::move(_f.a0), std::move(_result));
        }
      }
      return _result;
    }
  };

  struct list_expr {
    // TYPES
    struct LNil {};

    struct LCons {
      uint64_t a0;
      std::shared_ptr<list_expr> a1;
    };

    struct LAppend {
      std::shared_ptr<list_expr> a0;
      std::shared_ptr<list_expr> a1;
    };

    struct LReplicate {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<LNil, LCons, LAppend, LReplicate>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list_expr() {}

    explicit list_expr(LNil _v) : v_(_v) {}

    explicit list_expr(LCons _v) : v_(std::move(_v)) {}

    explicit list_expr(LAppend _v) : v_(std::move(_v)) {}

    explicit list_expr(LReplicate _v) : v_(std::move(_v)) {}

    static list_expr lnil() { return list_expr(LNil{}); }

    static list_expr lcons(uint64_t a0, list_expr a1) {
      return list_expr(LCons{a0, std::make_shared<list_expr>(std::move(a1))});
    }

    static list_expr lappend(list_expr a0, list_expr a1) {
      return list_expr(LAppend{std::make_shared<list_expr>(std::move(a0)),
                               std::make_shared<list_expr>(std::move(a1))});
    }

    static list_expr lreplicate(uint64_t a0, uint64_t a1) {
      return list_expr(LReplicate{a0, a1});
    }

    // MANIPULATORS
    ~list_expr() {
      crane::small_vector<std::shared_ptr<list_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LCons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<LAppend>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    list_expr(const list_expr &) = default;
    list_expr &operator=(const list_expr &) = default;
    list_expr(list_expr &&) noexcept = default;
    list_expr &operator=(list_expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t list_expr_size() const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [a0, _s1], dispatches next recursive call.
      struct _After_LAppend {
        list_expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Resume_LCons: saves [_s0], resumes after recursive call with _result.
      struct _Resume_LCons {
        std::decay_t<decltype(UINT64_C(1))> _s0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_expr_size: _Enter -> _After_LAppend -> _Combine_LAppend
      /// -> _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            _result = UINT64_C(1);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(_Combine_LAppend{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = (_f._s0 + std::move(_result));
        }
      }
      return _result;
    }

    List<uint64_t> eval_list() const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [a0], dispatches next recursive call.
      struct _After_LAppend {
        list_expr *a0;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        List<uint64_t> _result;
      };

      /// _Resume_LCons: saves [a0], resumes after recursive call with _result.
      struct _Resume_LCons {
        uint64_t a0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      List<uint64_t> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_list: _Enter -> _After_LAppend -> _Combine_LAppend ->
      /// _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = List<uint64_t>::nil();
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = ListDef::template repeat<uint64_t>(a1, a0);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(_Combine_LAppend{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = std::move(_result).app(std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = List<uint64_t>::cons(_f.a0, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, list_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, list_expr &, T1 &, list_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &>
    T1 list_expr_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [a0_0, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_LAppend {
        list_expr *a0_0;
        list_expr a1;
        list_expr a0_1;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        std::decay_t<T1> _result;
        list_expr a1;
        list_expr a0;
      };

      /// _Resume_LCons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_LCons {
        list_expr a1;
        uint64_t a0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_expr_rec: _Enter -> _After_LAppend -> _Combine_LAppend
      /// -> _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(a0, a1);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(_Combine_LAppend{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, list_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, list_expr &, T1 &, list_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &>
    T1 list_expr_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [a0_0, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_LAppend {
        list_expr *a0_0;
        list_expr a1;
        list_expr a0_1;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        std::decay_t<T1> _result;
        list_expr a1;
        list_expr a0;
      };

      /// _Resume_LCons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_LCons {
        list_expr a1;
        uint64_t a0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_expr_rect: _Enter -> _After_LAppend -> _Combine_LAppend
      /// -> _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(a0, a1);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(_Combine_LAppend{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };
};

template <typename T1> List<T1> ListDef::repeat(T1 x, uint64_t n) {
  std::shared_ptr<List<T1>> _head{};
  std::shared_ptr<List<T1>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<T1>>(List<T1>::nil());
      break;
    } else {
      uint64_t k = _loop_n - 1;
      auto _cell =
          std::make_shared<List<T1>>(typename List<T1>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_head);
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
