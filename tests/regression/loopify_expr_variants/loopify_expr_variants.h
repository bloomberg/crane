#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

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

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(const T1 &x, uint64_t n);
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

    static cond_expr add(crane::shared_child_slot<cond_expr> a0,
                         crane::shared_child_slot<cond_expr> a1) {
      return cond_expr(Add{a0.take(), a1.take()});
    }

    static cond_expr cond(crane::shared_child_slot<cond_expr> a0,
                          crane::shared_child_slot<cond_expr> a1,
                          crane::shared_child_slot<cond_expr> a2) {
      return cond_expr(Cond{a0.take(), a1.take(), a2.take()});
    }

    // MANIPULATORS
    ~cond_expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Add>(&v_mut())) {
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
      crane::small_vector<std::shared_ptr<cond_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
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

    cond_expr(const cond_expr &) = default;
    cond_expr &operator=(const cond_expr &) = default;
    cond_expr(cond_expr &&) = default;
    cond_expr &operator=(cond_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t size_cond() const {
      const cond_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of size_cond: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const cond_expr *_self;
      };

      struct _after_size_cond_in_Add {
        const cond_expr *a1;
      };

      struct _after_size_cond_in_Add_2 {
        uint64_t _tmp2;
      };

      struct _after_size_cond_in_Cond {
        const cond_expr *a1;
        const cond_expr *a2;
      };

      struct _after_size_cond_in_Cond_2 {
        const cond_expr *a2;
        uint64_t _tmp5;
      };

      struct _after_size_cond_in_Cond_3 {
        uint64_t _tmp5;
        uint64_t _tmp4;
      };

      using _frame =
          std::variant<_call, _after_size_cond_in_Add,
                       _after_size_cond_in_Add_2, _after_size_cond_in_Cond,
                       _after_size_cond_in_Cond_2, _after_size_cond_in_Cond_3>;
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
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_after_size_cond_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_size_cond_in_Cond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_size_cond_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_size_cond_in_Add>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_size_cond_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_size_cond_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_size_cond_in_Add_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
        } else if (std::holds_alternative<_after_size_cond_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_size_cond_in_Cond>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(
              _after_size_cond_in_Cond_2{&a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_size_cond_in_Cond_2>(_popped)) {
          auto _f = std::move(std::get<_after_size_cond_in_Cond_2>(_popped));
          _stack.pop_back();
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(
              _after_size_cond_in_Cond_3{_f._tmp5, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_size_cond_in_Cond_3>(_popped));
          _stack.pop_back();
          _result =
              (((UINT64_C(1) + _f._tmp5) + _f._tmp4) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval_cond() const {
      const cond_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_cond: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const cond_expr *_self;
      };

      struct _after_eval_cond_in_Add {
        const cond_expr *a1;
      };

      struct _after_eval_cond_in_Add_2 {
        uint64_t _tmp2;
      };

      struct _after_eval_cond_in_Cond {
        const cond_expr *a1;
        const cond_expr *a2;
      };

      using _frame =
          std::variant<_call, _after_eval_cond_in_Add,
                       _after_eval_cond_in_Add_2, _after_eval_cond_in_Cond>;
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
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_after_eval_cond_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_eval_cond_in_Cond{crane_raw(a1), crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_cond_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_eval_cond_in_Add>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_cond_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_cond_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_cond_in_Add_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_eval_cond_in_Cond>(_popped));
          _stack.pop_back();
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          if (UINT64_C(0) < std::move(_result)) {
            _stack.emplace_back(_call{_f.a1});
          } else {
            _stack.emplace_back(_call{_f.a2});
          }
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

      struct _after_cond_expr_rect_in_Add {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
      };

      struct _after_cond_expr_rect_in_Add_2 {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        T1 _tmp2;
      };

      struct _after_cond_expr_rect_in_Cond {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        const cond_expr *a2;
      };

      struct _after_cond_expr_rect_in_Cond_2 {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        const cond_expr *a2;
        T1 _tmp5;
      };

      struct _after_cond_expr_rect_in_Cond_3 {
        std::shared_ptr<cond_expr> a0;
        const cond_expr *a1;
        const cond_expr *a2;
        T1 _tmp5;
        T1 _tmp4;
      };

      using _frame = std::variant<
          _call, _after_cond_expr_rect_in_Add, _after_cond_expr_rect_in_Add_2,
          _after_cond_expr_rect_in_Cond, _after_cond_expr_rect_in_Cond_2,
          _after_cond_expr_rect_in_Cond_3>;
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
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_after_cond_expr_rect_in_Add{a0,
                                                             crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _after_cond_expr_rect_in_Cond{a0, crane_raw(a1),
                                              crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_cond_expr_rect_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_cond_expr_rect_in_Add>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_cond_expr_rect_in_Add_2{std::move(a0), &a1,
                                             std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_cond_expr_rect_in_Add_2>(_popped)) {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_Add_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        } else if (
                std::holds_alternative<_after_cond_expr_rect_in_Cond>(_popped)) {
          auto _f = std::move(std::get<_after_cond_expr_rect_in_Cond>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_cond_expr_rect_in_Cond_2{
              std::move(a0), &a1, &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_cond_expr_rect_in_Cond_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_Cond_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _stack.emplace_back(_after_cond_expr_rect_in_Cond_3{
              std::move(a0), &a1, &a2, std::move(_f._tmp5),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f =
              std::move(std::get<_after_cond_expr_rect_in_Cond_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          const cond_expr &a1 = *_f.a1;
          const cond_expr &a2 = *_f.a2;
          _result = f1(*a0, std::move(_f._tmp5), a1, std::move(_f._tmp4), a2,
                       std::move(_result));
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

    static arith_expr aadd(crane::shared_child_slot<arith_expr> a0,
                           crane::shared_child_slot<arith_expr> a1) {
      return arith_expr(AAdd{a0.take(), a1.take()});
    }

    static arith_expr amul(crane::shared_child_slot<arith_expr> a0,
                           crane::shared_child_slot<arith_expr> a1) {
      return arith_expr(AMul{a0.take(), a1.take()});
    }

    static arith_expr adiv(crane::shared_child_slot<arith_expr> a0,
                           crane::shared_child_slot<arith_expr> a1) {
      return arith_expr(ADiv{a0.take(), a1.take()});
    }

    // MANIPULATORS
    ~arith_expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<ANum>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<AAdd>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<AMul>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<ADiv>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<arith_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<AAdd>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<AMul>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<ADiv>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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
    arith_expr(arith_expr &&) = default;
    arith_expr &operator=(arith_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t count_ops() const {
      const arith_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of count_ops: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const arith_expr *_self;
      };

      struct _after_count_ops_in_AAdd {
        const arith_expr *a1;
      };

      struct _after_count_ops_in_AAdd_2 {
        uint64_t _tmp2;
      };

      struct _after_count_ops_in_ADiv {
        const arith_expr *a1;
      };

      struct _after_count_ops_in_ADiv_2 {
        uint64_t _tmp6;
      };

      struct _after_count_ops_in_AMul {
        const arith_expr *a1;
      };

      struct _after_count_ops_in_AMul_2 {
        uint64_t _tmp4;
      };

      using _frame = std::variant<
          _call, _after_count_ops_in_AAdd, _after_count_ops_in_AAdd_2,
          _after_count_ops_in_ADiv, _after_count_ops_in_ADiv_2,
          _after_count_ops_in_AMul, _after_count_ops_in_AMul_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_after_count_ops_in_AAdd{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_after_count_ops_in_AMul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_after_count_ops_in_ADiv{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_count_ops_in_AAdd>(_popped)) {
          auto _f = std::move(std::get<_after_count_ops_in_AAdd>(_popped));
          _stack.pop_back();
          const arith_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_count_ops_in_AAdd_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_count_ops_in_AAdd_2>(_popped)) {
          auto _f = std::move(std::get<_after_count_ops_in_AAdd_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
        } else if (std::holds_alternative<_after_count_ops_in_ADiv>(_popped)) {
          auto _f = std::move(std::get<_after_count_ops_in_ADiv>(_popped));
          _stack.pop_back();
          const arith_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_count_ops_in_ADiv_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_count_ops_in_ADiv_2>(_popped)) {
          auto _f = std::move(std::get<_after_count_ops_in_ADiv_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp6) + std::move(_result));
        } else if (std::holds_alternative<_after_count_ops_in_AMul>(_popped)) {
          auto _f = std::move(std::get<_after_count_ops_in_AMul>(_popped));
          _stack.pop_back();
          const arith_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_count_ops_in_AMul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_count_ops_in_AMul_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp4) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval_arith() const {
      const arith_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_arith: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const arith_expr *_self;
      };

      struct _after_eval_arith_in_AAdd {
        const arith_expr *a1;
      };

      struct _after_eval_arith_in_AAdd_2 {
        uint64_t _tmp2;
      };

      struct _after_eval_arith_in_ADiv {
        const arith_expr *a0;
      };

      struct _after_eval_arith_in_AMul {
        const arith_expr *a1;
      };

      struct _after_eval_arith_in_AMul_2 {
        uint64_t _tmp4;
      };

      struct _after_eval_arith_in_S {
        uint64_t n;
      };

      using _frame = std::variant<
          _call, _after_eval_arith_in_AAdd, _after_eval_arith_in_AAdd_2,
          _after_eval_arith_in_ADiv, _after_eval_arith_in_AMul,
          _after_eval_arith_in_AMul_2, _after_eval_arith_in_S>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_after_eval_arith_in_AAdd{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_after_eval_arith_in_AMul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_after_eval_arith_in_ADiv{crane_raw(a0)});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_after_eval_arith_in_AAdd>(_popped)) {
          auto _f = std::move(std::get<_after_eval_arith_in_AAdd>(_popped));
          _stack.pop_back();
          const arith_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_arith_in_AAdd_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_arith_in_AAdd_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_arith_in_AAdd_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<_after_eval_arith_in_ADiv>(_popped)) {
          auto _f = std::move(std::get<_after_eval_arith_in_ADiv>(_popped));
          _stack.pop_back();
          const arith_expr &a0 = *_f.a0;
          uint64_t _tmp6 = std::move(_result);
          if (_tmp6 <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t n = _tmp6 - 1;
            _stack.emplace_back(_after_eval_arith_in_S{n});
            _stack.emplace_back(_call{_f.a0});
          }
        } else if (std::holds_alternative<_after_eval_arith_in_AMul>(_popped)) {
          auto _f = std::move(std::get<_after_eval_arith_in_AMul>(_popped));
          _stack.pop_back();
          const arith_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_arith_in_AMul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_arith_in_AMul_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_arith_in_AMul_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp4 * std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_eval_arith_in_S>(_popped));
          _stack.pop_back();
          uint64_t n = _f.n;
          auto &&_once1 = (n + 1);
          _result = (_once1 ? std::move(_result) / _once1 : 0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
    T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      return this->template arith_expr_rect<T1>(f, f0, f1, f2);
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of arith_expr_rect:
      // _call frames are pending calls, _after frames resume a caller.
      struct _call {
        const arith_expr *_self;
      };

      struct _after_arith_expr_rect_in_AAdd {
        std::shared_ptr<arith_expr> a2;
        const arith_expr *a3;
      };

      struct _after_arith_expr_rect_in_AAdd_2 {
        std::shared_ptr<arith_expr> a2;
        const arith_expr *a3;
        T1 _tmp2;
      };

      struct _after_arith_expr_rect_in_ADiv {
        std::shared_ptr<arith_expr> a2;
        const arith_expr *a3;
      };

      struct _after_arith_expr_rect_in_ADiv_2 {
        std::shared_ptr<arith_expr> a2;
        const arith_expr *a3;
        T1 _tmp6;
      };

      struct _after_arith_expr_rect_in_AMul {
        std::shared_ptr<arith_expr> a2;
        const arith_expr *a3;
      };

      struct _after_arith_expr_rect_in_AMul_2 {
        std::shared_ptr<arith_expr> a2;
        const arith_expr *a3;
        T1 _tmp4;
      };

      using _frame = std::variant<
          _call, _after_arith_expr_rect_in_AAdd,
          _after_arith_expr_rect_in_AAdd_2, _after_arith_expr_rect_in_ADiv,
          _after_arith_expr_rect_in_ADiv_2, _after_arith_expr_rect_in_AMul,
          _after_arith_expr_rect_in_AMul_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(_sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(
                _after_arith_expr_rect_in_AAdd{a2, crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a2)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(_sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(
                _after_arith_expr_rect_in_AMul{a2, crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a2)});
          } else {
            const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(
                _after_arith_expr_rect_in_ADiv{a2, crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a2)});
          }
        } else if (
                std::holds_alternative<_after_arith_expr_rect_in_AAdd>(_popped)) {
          auto _f =
              std::move(std::get<_after_arith_expr_rect_in_AAdd>(_popped));
          _stack.pop_back();
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          const arith_expr &a3 = *_f.a3;
          _stack.emplace_back(_after_arith_expr_rect_in_AAdd_2{
              std::move(a2), &a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else if (std::holds_alternative<_after_arith_expr_rect_in_AAdd_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_arith_expr_rect_in_AAdd_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          const arith_expr &a3 = *_f.a3;
          _result = f0(*a2, std::move(_f._tmp2), a3, std::move(_result));
        } else if (
                std::holds_alternative<_after_arith_expr_rect_in_ADiv>(_popped)) {
          auto _f =
              std::move(std::get<_after_arith_expr_rect_in_ADiv>(_popped));
          _stack.pop_back();
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          const arith_expr &a3 = *_f.a3;
          _stack.emplace_back(_after_arith_expr_rect_in_ADiv_2{
              std::move(a2), &a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else if (std::holds_alternative<_after_arith_expr_rect_in_ADiv_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_arith_expr_rect_in_ADiv_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          const arith_expr &a3 = *_f.a3;
          _result = f2(*a2, std::move(_f._tmp6), a3, std::move(_result));
        } else if (
                std::holds_alternative<_after_arith_expr_rect_in_AMul>(_popped)) {
          auto _f =
              std::move(std::get<_after_arith_expr_rect_in_AMul>(_popped));
          _stack.pop_back();
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          const arith_expr &a3 = *_f.a3;
          _stack.emplace_back(_after_arith_expr_rect_in_AMul_2{
              std::move(a2), &a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f =
              std::move(std::get<_after_arith_expr_rect_in_AMul_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          const arith_expr &a3 = *_f.a3;
          _result = f1(*a2, std::move(_f._tmp4), a3, std::move(_result));
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

    static bool_expr band(crane::shared_child_slot<bool_expr> a0,
                          crane::shared_child_slot<bool_expr> a1) {
      return bool_expr(BAnd{a0.take(), a1.take()});
    }

    static bool_expr bor(crane::shared_child_slot<bool_expr> a0,
                         crane::shared_child_slot<bool_expr> a1) {
      return bool_expr(BOr{a0.take(), a1.take()});
    }

    static bool_expr bnot(crane::shared_child_slot<bool_expr> a0) {
      return bool_expr(BNot{a0.take()});
    }

    // MANIPULATORS
    ~bool_expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<BTrue>(v_mut())) {
        return;
      }
      if (std::holds_alternative<BFalse>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<BAnd>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<BOr>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<BNot>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<bool_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BAnd>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BOr>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BNot>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
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
    bool_expr(bool_expr &&) = default;
    bool_expr &operator=(bool_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool_expr simplify_bool() const {
      const bool_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of simplify_bool: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bool_expr *_self;
      };

      struct _after_simplify_bool_in_BAnd {
        const bool_expr *a1;
      };

      struct _after_simplify_bool_in_BAnd_2 {
        bool_expr a_;
      };

      struct _after_simplify_bool_in_BAnd_3 {
        bool_expr a_;
      };

      struct _after_simplify_bool_in_BFalse {};

      struct _after_simplify_bool_in_BNot {
        bool_expr a_;
      };

      struct _after_simplify_bool_in_BNot_2 {
        bool_expr a_;
      };

      struct _after_simplify_bool_in_BNot_3 {};

      struct _after_simplify_bool_in_BOr {
        bool_expr a_;
      };

      struct _after_simplify_bool_in_BOr_2 {
        const bool_expr *a1;
      };

      struct _after_simplify_bool_in_BOr_3 {
        bool_expr a_;
      };

      struct _after_simplify_bool_in_BTrue {};

      using _frame = std::variant<
          _call, _after_simplify_bool_in_BAnd, _after_simplify_bool_in_BAnd_2,
          _after_simplify_bool_in_BAnd_3, _after_simplify_bool_in_BFalse,
          _after_simplify_bool_in_BNot, _after_simplify_bool_in_BNot_2,
          _after_simplify_bool_in_BNot_3, _after_simplify_bool_in_BOr,
          _after_simplify_bool_in_BOr_2, _after_simplify_bool_in_BOr_3,
          _after_simplify_bool_in_BTrue>;
      bool_expr _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = bool_expr::btrue();
          } else if (
                  std::holds_alternative<typename bool_expr::BFalse>(_sv.v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_after_simplify_bool_in_BAnd{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_after_simplify_bool_in_BOr_2{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_after_simplify_bool_in_BNot_3{});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BAnd>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_bool_in_BAnd>(_popped));
          _stack.pop_back();
          const bool_expr &a1 = *_f.a1;
          bool_expr _tmp5 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp5.v_mut())) {
            _stack.emplace_back(_after_simplify_bool_in_BTrue{});
            _stack.emplace_back(_call{_f.a1});
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp5.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp5.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_tmp5.v_mut());
            bool_expr a_ = bool_expr::band(crane::shared_child(a00),
                                           crane::shared_child(a10));
            _stack.emplace_back(_after_simplify_bool_in_BAnd_2{std::move(a_)});
            _stack.emplace_back(_call{_f.a1});
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp5.v_mut())) {
            auto &[a00, a10] = std::get<typename bool_expr::BOr>(_tmp5.v_mut());
            bool_expr a_ = bool_expr::bor(crane::shared_child(a00),
                                          crane::shared_child(a10));
            _stack.emplace_back(_after_simplify_bool_in_BOr{std::move(a_)});
            _stack.emplace_back(_call{_f.a1});
          } else {
            auto &[a00] = std::get<typename bool_expr::BNot>(_tmp5.v_mut());
            bool_expr a_ = bool_expr::bnot(crane::shared_child(a00));
            _stack.emplace_back(_after_simplify_bool_in_BNot{std::move(a_)});
            _stack.emplace_back(_call{_f.a1});
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BAnd_2>(_popped)) {
          auto _f =
              std::move(std::get<_after_simplify_bool_in_BAnd_2>(_popped));
          _stack.pop_back();
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp2 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp2.v_mut())) {
            _result = std::move(a_);
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp2.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp2.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp2.v_mut());
            _result = bool_expr::band(std::move(a_),
                                      bool_expr::band(crane::shared_child(a01),
                                                      crane::shared_child(a11)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp2.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp2.v_mut());
            _result = bool_expr::band(std::move(a_),
                                      bool_expr::bor(crane::shared_child(a01),
                                                     crane::shared_child(a11)));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp2.v_mut());
            _result =
                bool_expr::band(std::move(a_),
                                bool_expr::bnot(crane::shared_child(a01)));
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BAnd_3>(_popped)) {
          auto _f =
              std::move(std::get<_after_simplify_bool_in_BAnd_3>(_popped));
          _stack.pop_back();
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp7 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp7.v_mut())) {
            _result = bool_expr::btrue();
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp7.v_mut())) {
            _result = std::move(a_);
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp7.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp7.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::band(crane::shared_child(a01),
                                                     crane::shared_child(a11)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp7.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp7.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::bor(crane::shared_child(a01),
                                                    crane::shared_child(a11)));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp7.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::bnot(crane::shared_child(a01)));
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BFalse>(_popped)) {
          auto _f =
              std::move(std::get<_after_simplify_bool_in_BFalse>(_popped));
          _stack.pop_back();
          bool_expr _tmp6 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp6.v_mut())) {
            _result = bool_expr::btrue();
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp6.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp6.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp6.v_mut());
            _result = bool_expr::band(crane::shared_child(a01),
                                      crane::shared_child(a11));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp6.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp6.v_mut());
            _result = bool_expr::bor(crane::shared_child(a01),
                                     crane::shared_child(a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp6.v_mut());
            _result = bool_expr::bnot(crane::shared_child(a01));
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BNot>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_bool_in_BNot>(_popped));
          _stack.pop_back();
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp4 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp4.v_mut())) {
            _result = std::move(a_);
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp4.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp4.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp4.v_mut());
            _result = bool_expr::band(std::move(a_),
                                      bool_expr::band(crane::shared_child(a01),
                                                      crane::shared_child(a11)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp4.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp4.v_mut());
            _result = bool_expr::band(std::move(a_),
                                      bool_expr::bor(crane::shared_child(a01),
                                                     crane::shared_child(a11)));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp4.v_mut());
            _result =
                bool_expr::band(std::move(a_),
                                bool_expr::bnot(crane::shared_child(a01)));
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BNot_2>(_popped)) {
          auto _f =
              std::move(std::get<_after_simplify_bool_in_BNot_2>(_popped));
          _stack.pop_back();
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp9 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp9.v_mut())) {
            _result = bool_expr::btrue();
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp9.v_mut())) {
            _result = std::move(a_);
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp9.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp9.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::band(crane::shared_child(a01),
                                                     crane::shared_child(a11)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp9.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp9.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::bor(crane::shared_child(a01),
                                                    crane::shared_child(a11)));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp9.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::bnot(crane::shared_child(a01)));
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BNot_3>(_popped)) {
          auto _f =
              std::move(std::get<_after_simplify_bool_in_BNot_3>(_popped));
          _stack.pop_back();
          bool_expr _tmp11 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp11.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp11.v_mut())) {
            _result = bool_expr::btrue();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp11.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_tmp11.v_mut());
            _result =
                bool_expr::bnot(bool_expr::band(crane::shared_child(a00),
                                                crane::shared_child(a10)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp11.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_tmp11.v_mut());
            _result = bool_expr::bnot(bool_expr::bor(crane::shared_child(a00),
                                                     crane::shared_child(a10)));
          } else {
            auto &[a00] = std::get<typename bool_expr::BNot>(_tmp11.v_mut());
            _result =
                bool_expr::bnot(bool_expr::bnot(crane::shared_child(a00)));
          }
        } else if (std::holds_alternative<_after_simplify_bool_in_BOr>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_bool_in_BOr>(_popped));
          _stack.pop_back();
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp3 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp3.v_mut())) {
            _result = std::move(a_);
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp3.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp3.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp3.v_mut());
            _result = bool_expr::band(std::move(a_),
                                      bool_expr::band(crane::shared_child(a01),
                                                      crane::shared_child(a11)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp3.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp3.v_mut());
            _result = bool_expr::band(std::move(a_),
                                      bool_expr::bor(crane::shared_child(a01),
                                                     crane::shared_child(a11)));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp3.v_mut());
            _result =
                bool_expr::band(std::move(a_),
                                bool_expr::bnot(crane::shared_child(a01)));
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BOr_2>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_bool_in_BOr_2>(_popped));
          _stack.pop_back();
          const bool_expr &a1 = *_f.a1;
          bool_expr _tmp10 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp10.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp10.v_mut())) {
            _stack.emplace_back(_after_simplify_bool_in_BFalse{});
            _stack.emplace_back(_call{_f.a1});
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp10.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_tmp10.v_mut());
            bool_expr a_ = bool_expr::band(crane::shared_child(a00),
                                           crane::shared_child(a10));
            _stack.emplace_back(_after_simplify_bool_in_BAnd_3{std::move(a_)});
            _stack.emplace_back(_call{_f.a1});
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp10.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_tmp10.v_mut());
            bool_expr a_ = bool_expr::bor(crane::shared_child(a00),
                                          crane::shared_child(a10));
            _stack.emplace_back(_after_simplify_bool_in_BOr_3{std::move(a_)});
            _stack.emplace_back(_call{_f.a1});
          } else {
            auto &[a00] = std::get<typename bool_expr::BNot>(_tmp10.v_mut());
            bool_expr a_ = bool_expr::bnot(crane::shared_child(a00));
            _stack.emplace_back(_after_simplify_bool_in_BNot_2{std::move(a_)});
            _stack.emplace_back(_call{_f.a1});
          }
        } else if (
                std::holds_alternative<_after_simplify_bool_in_BOr_3>(_popped)) {
          auto _f = std::move(std::get<_after_simplify_bool_in_BOr_3>(_popped));
          _stack.pop_back();
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp8 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp8.v_mut())) {
            _result = bool_expr::btrue();
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp8.v_mut())) {
            _result = std::move(a_);
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp8.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp8.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::band(crane::shared_child(a01),
                                                     crane::shared_child(a11)));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp8.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp8.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::bor(crane::shared_child(a01),
                                                    crane::shared_child(a11)));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp8.v_mut());
            _result = bool_expr::bor(std::move(a_),
                                     bool_expr::bnot(crane::shared_child(a01)));
          }
        } else {
          auto _f = std::move(std::get<_after_simplify_bool_in_BTrue>(_popped));
          _stack.pop_back();
          bool_expr _tmp1 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(_tmp1.v_mut())) {
            _result = bool_expr::btrue();
          } else if (
              std::holds_alternative<typename bool_expr::BFalse>(_tmp1.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (
              std::holds_alternative<typename bool_expr::BAnd>(_tmp1.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp1.v_mut());
            _result = bool_expr::band(crane::shared_child(a01),
                                      crane::shared_child(a11));
          } else if (
              std::holds_alternative<typename bool_expr::BOr>(_tmp1.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp1.v_mut());
            _result = bool_expr::bor(crane::shared_child(a01),
                                     crane::shared_child(a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp1.v_mut());
            _result = bool_expr::bnot(crane::shared_child(a01));
          }
        }
      }
      return _result;
    }

    bool eval_bool() const {
      const bool_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_bool: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bool_expr *_self;
      };

      struct _after_eval_bool_in_BAnd {
        const bool_expr *a1;
      };

      struct _after_eval_bool_in_BAnd_2 {
        bool _tmp2;
      };

      struct _after_eval_bool_in_BNot {};

      struct _after_eval_bool_in_BOr {
        const bool_expr *a1;
      };

      struct _after_eval_bool_in_BOr_2 {
        bool _tmp4;
      };

      using _frame =
          std::variant<_call, _after_eval_bool_in_BAnd,
                       _after_eval_bool_in_BAnd_2, _after_eval_bool_in_BNot,
                       _after_eval_bool_in_BOr, _after_eval_bool_in_BOr_2>;
      bool _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = true;
          } else if (
                  std::holds_alternative<typename bool_expr::BFalse>(_sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_after_eval_bool_in_BAnd{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_after_eval_bool_in_BOr{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_after_eval_bool_in_BNot{});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_bool_in_BAnd>(_popped)) {
          auto _f = std::move(std::get<_after_eval_bool_in_BAnd>(_popped));
          _stack.pop_back();
          const bool_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_bool_in_BAnd_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_bool_in_BAnd_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_bool_in_BAnd_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 && std::move(_result));
        } else if (std::holds_alternative<_after_eval_bool_in_BNot>(_popped)) {
          auto _f = std::move(std::get<_after_eval_bool_in_BNot>(_popped));
          _stack.pop_back();
          _result = !(std::move(_result));
        } else if (std::holds_alternative<_after_eval_bool_in_BOr>(_popped)) {
          auto _f = std::move(std::get<_after_eval_bool_in_BOr>(_popped));
          _stack.pop_back();
          const bool_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_bool_in_BOr_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_eval_bool_in_BOr_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp4 || std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 bool_expr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      return this->template bool_expr_rect<T1>(std::move(f), std::move(f0), f1,
                                               f2, f3);
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 bool_expr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of bool_expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bool_expr *_self;
      };

      struct _after_bool_expr_rect_in_BAnd {
        std::shared_ptr<bool_expr> a0;
        const bool_expr *a1;
      };

      struct _after_bool_expr_rect_in_BAnd_2 {
        std::shared_ptr<bool_expr> a0;
        const bool_expr *a1;
        T1 _tmp2;
      };

      struct _after_bool_expr_rect_in_BNot {
        std::shared_ptr<bool_expr> a0;
      };

      struct _after_bool_expr_rect_in_BOr {
        std::shared_ptr<bool_expr> a0;
        const bool_expr *a1;
      };

      struct _after_bool_expr_rect_in_BOr_2 {
        std::shared_ptr<bool_expr> a0;
        const bool_expr *a1;
        T1 _tmp4;
      };

      using _frame = std::variant<
          _call, _after_bool_expr_rect_in_BAnd, _after_bool_expr_rect_in_BAnd_2,
          _after_bool_expr_rect_in_BNot, _after_bool_expr_rect_in_BOr,
          _after_bool_expr_rect_in_BOr_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = f;
          } else if (
                  std::holds_alternative<typename bool_expr::BFalse>(_sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(
                _after_bool_expr_rect_in_BAnd{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_after_bool_expr_rect_in_BOr{a0,
                                                             crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_after_bool_expr_rect_in_BNot{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_bool_expr_rect_in_BAnd>(_popped)) {
          auto _f = std::move(std::get<_after_bool_expr_rect_in_BAnd>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          const bool_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_bool_expr_rect_in_BAnd_2{
              std::move(a0), &a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_bool_expr_rect_in_BAnd_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_bool_expr_rect_in_BAnd_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          const bool_expr &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp2), a1, std::move(_result));
        } else if (
                std::holds_alternative<_after_bool_expr_rect_in_BNot>(_popped)) {
          auto _f = std::move(std::get<_after_bool_expr_rect_in_BNot>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          _result = f3(*a0, std::move(_result));
        } else if (
                std::holds_alternative<_after_bool_expr_rect_in_BOr>(_popped)) {
          auto _f = std::move(std::get<_after_bool_expr_rect_in_BOr>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          const bool_expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_bool_expr_rect_in_BOr_2{std::move(a0), &a1,
                                             std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_bool_expr_rect_in_BOr_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          const bool_expr &a1 = *_f.a1;
          _result = f2(*a0, std::move(_f._tmp4), a1, std::move(_result));
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

    static list_expr lcons(uint64_t a0,
                           crane::shared_child_slot<list_expr> a1) {
      return list_expr(LCons{a0, a1.take()});
    }

    static list_expr lappend(crane::shared_child_slot<list_expr> a0,
                             crane::shared_child_slot<list_expr> a1) {
      return list_expr(LAppend{a0.take(), a1.take()});
    }

    static list_expr lreplicate(uint64_t a0, uint64_t a1) {
      return list_expr(LReplicate{a0, a1});
    }

    // MANIPULATORS
    ~list_expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<LNil>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<LCons>(&v_mut())) {
        if (!(_alt->a1 && _alt->a1.use_count() == 1)) {
          return;
        }
      }
      if (auto *_alt = std::get_if<LAppend>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (std::holds_alternative<LReplicate>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<list_expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LCons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<LAppend>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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
    list_expr(list_expr &&) = default;
    list_expr &operator=(list_expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t list_expr_size() const {
      const list_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of list_expr_size: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const list_expr *_self;
      };

      struct _after_list_expr_size_in_LAppend {
        const list_expr *a1;
      };

      struct _after_list_expr_size_in_LAppend_2 {
        uint64_t _tmp3;
      };

      struct _after_list_expr_size_in_LCons {};

      using _frame = std::variant<_call, _after_list_expr_size_in_LAppend,
                                  _after_list_expr_size_in_LAppend_2,
                                  _after_list_expr_size_in_LCons>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[_, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_after_list_expr_size_in_LCons{});
            _stack.emplace_back(_call{crane_raw(a1)});
          } else if (
                  std::holds_alternative<typename list_expr::LAppend>(_sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_after_list_expr_size_in_LAppend{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            _result = UINT64_C(1);
          }
        } else if (std::holds_alternative<_after_list_expr_size_in_LAppend>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_list_expr_size_in_LAppend>(_popped));
          _stack.pop_back();
          const list_expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_list_expr_size_in_LAppend_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_list_expr_size_in_LAppend_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_list_expr_size_in_LAppend_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp3) + std::move(_result));
        } else {
          auto _f =
              std::move(std::get<_after_list_expr_size_in_LCons>(_popped));
          _stack.pop_back();
          _result = (UINT64_C(1) + std::move(_result));
        }
      }
      return _result;
    }

    List<uint64_t> eval_list() const {
      const list_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_list: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const list_expr *_self;
      };

      struct _after_eval_list_in_LAppend {
        const list_expr *a1;
      };

      struct _after_eval_list_in_LAppend_2 {
        List<uint64_t> _tmp3;
      };

      struct _after_eval_list_in_LCons {
        uint64_t a0;
      };

      using _frame = std::variant<_call, _after_eval_list_in_LAppend,
                                  _after_eval_list_in_LAppend_2,
                                  _after_eval_list_in_LCons>;
      List<uint64_t> _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = List<uint64_t>::nil();
          } else if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_after_eval_list_in_LCons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          } else if (
                  std::holds_alternative<typename list_expr::LAppend>(_sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_after_eval_list_in_LAppend{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = ListDef::template repeat<uint64_t>(a1, a0);
          }
        } else if (std::holds_alternative<_after_eval_list_in_LAppend>(_popped)) {
          auto _f = std::move(std::get<_after_eval_list_in_LAppend>(_popped));
          _stack.pop_back();
          const list_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_list_in_LAppend_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_eval_list_in_LAppend_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_list_in_LAppend_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp3.app(std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_eval_list_in_LCons>(_popped));
          _stack.pop_back();
          uint64_t a0 = _f.a0;
          _result = List<uint64_t>::cons(a0, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1, typename F2, typename F3>
    T1 list_expr_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      return this->template list_expr_rect<T1>(std::move(f), f0, f1, f2);
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F3 &, const uint64_t &,
                                     const uint64_t &>
    T1 list_expr_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      // Explicit stack replaces the non-tail recursion of list_expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const list_expr *_self;
      };

      struct _after_list_expr_rect_in_LAppend {
        std::shared_ptr<list_expr> a0;
        const list_expr *a1;
      };

      struct _after_list_expr_rect_in_LAppend_2 {
        std::shared_ptr<list_expr> a0;
        const list_expr *a1;
        T1 _tmp3;
      };

      struct _after_list_expr_rect_in_LCons {
        uint64_t a0;
        std::shared_ptr<list_expr> a1;
      };

      using _frame = std::variant<_call, _after_list_expr_rect_in_LAppend,
                                  _after_list_expr_rect_in_LAppend_2,
                                  _after_list_expr_rect_in_LCons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_after_list_expr_rect_in_LCons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          } else if (
                  std::holds_alternative<typename list_expr::LAppend>(_sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(
                _after_list_expr_rect_in_LAppend{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(a0, a1);
          }
        } else if (std::holds_alternative<_after_list_expr_rect_in_LAppend>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_list_expr_rect_in_LAppend>(_popped));
          _stack.pop_back();
          std::shared_ptr<list_expr> a0 = std::move(_f.a0);
          const list_expr &a1 = *_f.a1;
          _stack.emplace_back(_after_list_expr_rect_in_LAppend_2{
              std::move(a0), &a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_list_expr_rect_in_LAppend_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_list_expr_rect_in_LAppend_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<list_expr> a0 = std::move(_f.a0);
          const list_expr &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp3), a1, std::move(_result));
        } else {
          auto _f =
              std::move(std::get<_after_list_expr_rect_in_LCons>(_popped));
          _stack.pop_back();
          uint64_t a0 = _f.a0;
          std::shared_ptr<list_expr> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };
};

template <typename T1> List<T1> ListDef::repeat(const T1 &x, uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<T1>> _root{};
  std::shared_ptr<List<T1>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<T1>::nil();
      (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t k = _loop_n - 1;
      auto _cell = typename List<T1>::Cons(x, nullptr);
      List<T1> &_node =
          (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_root);
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
