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

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp5, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_1 {
        uint64_t _tmp5;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp4, _tmp5], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Cond_2 {
        uint64_t _tmp4;
        uint64_t _tmp5;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified size_cond: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond -> CraneCont_Cond_1 -> CraneCont_Cond_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_1{std::move(_result), std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_2{std::move(_result), _f._tmp5});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          _result =
              (((UINT64_C(1) + _f._tmp5) + _f._tmp4) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval_cond() const {
      const cond_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_Cond: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Add,
                                      CraneCont_Add_1, CraneCont_Cond>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_cond: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Cond.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          uint64_t _tmp3 = std::move(_result);
          if (UINT64_C(0) < _tmp3) {
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const cond_expr *_self;
      };

      /// CraneCont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Add_1 {
        T1 _tmp2;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
      };

      /// CraneCont_Cond: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cond {
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_Cond_1: saves [_tmp5, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Cond_1 {
        T1 _tmp5;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      /// CraneCont_Cond_2: saves [_tmp4, _tmp5, a0, a1, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Cond_2 {
        T1 _tmp4;
        T1 _tmp5;
        std::shared_ptr<cond_expr> a0;
        std::shared_ptr<cond_expr> a1;
        std::shared_ptr<cond_expr> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Cond, CraneCont_Cond_1, CraneCont_Cond_2>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified cond_expr_rect: CraneEnter -> CraneCont_Add ->
      /// CraneCont_Add_1 -> CraneCont_Cond -> CraneCont_Cond_1 ->
      /// CraneCont_Cond_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(CraneCont_Cond{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Add_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_Cond>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Cond_1{
              std::move(_result), std::move(a0), a1, std::move(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Cond_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Cond_1>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Cond_2{std::move(_result), std::move(_f._tmp5),
                               std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Cond_2>(_frame));
          std::shared_ptr<cond_expr> a0 = std::move(_f.a0);
          std::shared_ptr<cond_expr> a1 = std::move(_f.a1);
          std::shared_ptr<cond_expr> a2 = std::move(_f.a2);
          _result = f1(*a0, std::move(_f._tmp5), *a1, std::move(_f._tmp4), *a2,
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const arith_expr *_self;
      };

      /// CraneCont_AAdd: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AAdd {
        std::shared_ptr<arith_expr> a1;
      };

      /// CraneCont_AAdd_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AAdd_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_ADiv: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ADiv {
        std::shared_ptr<arith_expr> a1;
      };

      /// CraneCont_ADiv_1: saves [_tmp6], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ADiv_1 {
        uint64_t _tmp6;
      };

      /// CraneCont_AMul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AMul {
        std::shared_ptr<arith_expr> a1;
      };

      /// CraneCont_AMul_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AMul_1 {
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_AAdd, CraneCont_AAdd_1,
                       CraneCont_ADiv, CraneCont_ADiv_1, CraneCont_AMul,
                       CraneCont_AMul_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified count_ops: CraneEnter -> CraneCont_AAdd -> CraneCont_AAdd_1
      /// -> CraneCont_ADiv -> CraneCont_ADiv_1 -> CraneCont_AMul ->
      /// CraneCont_AMul_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(CraneCont_AAdd{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(CraneCont_AMul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(CraneCont_ADiv{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_AAdd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AAdd>(_frame));
          std::shared_ptr<arith_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_AAdd_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_AAdd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AAdd_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
        } else if (std::holds_alternative<CraneCont_ADiv>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ADiv>(_frame));
          std::shared_ptr<arith_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_ADiv_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_ADiv_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ADiv_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp6) + std::move(_result));
        } else if (std::holds_alternative<CraneCont_AMul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AMul>(_frame));
          std::shared_ptr<arith_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_AMul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_AMul_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp4) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval_arith() const {
      const arith_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const arith_expr *_self;
      };

      /// CraneCont_AAdd: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AAdd {
        std::shared_ptr<arith_expr> a1;
      };

      /// CraneCont_AAdd_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AAdd_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_ADiv: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ADiv {
        std::shared_ptr<arith_expr> a0;
      };

      /// CraneCont_AMul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AMul {
        std::shared_ptr<arith_expr> a1;
      };

      /// CraneCont_AMul_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AMul_1 {
        uint64_t _tmp4;
      };

      /// CraneCont_n: saves [n], resumes after recursive call, then processes
      /// rest.
      struct CraneCont_n {
        uint64_t n;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_AAdd, CraneCont_AAdd_1,
                       CraneCont_ADiv, CraneCont_AMul, CraneCont_AMul_1,
                       CraneCont_n>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_arith: CraneEnter -> CraneCont_AAdd -> CraneCont_AAdd_1
      /// -> CraneCont_ADiv -> CraneCont_AMul -> CraneCont_AMul_1 ->
      /// CraneCont_n.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(CraneCont_AAdd{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(CraneCont_AMul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(CraneCont_ADiv{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<CraneCont_AAdd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AAdd>(_frame));
          std::shared_ptr<arith_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_AAdd_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_AAdd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AAdd_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<CraneCont_ADiv>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ADiv>(_frame));
          std::shared_ptr<arith_expr> a0 = std::move(_f.a0);
          uint64_t _tmp6 = std::move(_result);
          if (_tmp6 <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t n = _tmp6 - 1;
            _stack.emplace_back(CraneCont_n{n});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_AMul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AMul>(_frame));
          std::shared_ptr<arith_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_AMul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_AMul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AMul_1>(_frame));
          _result = (_f._tmp4 * std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_n>(_frame));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const arith_expr *_self;
      };

      /// CraneCont_AAdd: saves [a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AAdd {
        std::shared_ptr<arith_expr> a2;
        std::shared_ptr<arith_expr> a3;
      };

      /// CraneCont_AAdd_1: saves [_tmp2, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_AAdd_1 {
        T1 _tmp2;
        std::shared_ptr<arith_expr> a2;
        std::shared_ptr<arith_expr> a3;
      };

      /// CraneCont_ADiv: saves [a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ADiv {
        std::shared_ptr<arith_expr> a2;
        std::shared_ptr<arith_expr> a3;
      };

      /// CraneCont_ADiv_1: saves [_tmp6, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_ADiv_1 {
        T1 _tmp6;
        std::shared_ptr<arith_expr> a2;
        std::shared_ptr<arith_expr> a3;
      };

      /// CraneCont_AMul: saves [a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AMul {
        std::shared_ptr<arith_expr> a2;
        std::shared_ptr<arith_expr> a3;
      };

      /// CraneCont_AMul_1: saves [_tmp4, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_AMul_1 {
        T1 _tmp4;
        std::shared_ptr<arith_expr> a2;
        std::shared_ptr<arith_expr> a3;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_AAdd, CraneCont_AAdd_1,
                       CraneCont_ADiv, CraneCont_ADiv_1, CraneCont_AMul,
                       CraneCont_AMul_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified arith_expr_rect: CraneEnter -> CraneCont_AAdd ->
      /// CraneCont_AAdd_1 -> CraneCont_ADiv -> CraneCont_ADiv_1 ->
      /// CraneCont_AMul -> CraneCont_AMul_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(CraneCont_AAdd{a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(CraneCont_AMul{a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          } else {
            const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(CraneCont_ADiv{a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<CraneCont_AAdd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AAdd>(_frame));
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          std::shared_ptr<arith_expr> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_AAdd_1{std::move(_result), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_AAdd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AAdd_1>(_frame));
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          std::shared_ptr<arith_expr> a3 = std::move(_f.a3);
          _result = f0(*a2, std::move(_f._tmp2), *a3, std::move(_result));
        } else if (std::holds_alternative<CraneCont_ADiv>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ADiv>(_frame));
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          std::shared_ptr<arith_expr> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_ADiv_1{std::move(_result), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_ADiv_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ADiv_1>(_frame));
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          std::shared_ptr<arith_expr> a3 = std::move(_f.a3);
          _result = f2(*a2, std::move(_f._tmp6), *a3, std::move(_result));
        } else if (std::holds_alternative<CraneCont_AMul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AMul>(_frame));
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          std::shared_ptr<arith_expr> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_AMul_1{std::move(_result), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_AMul_1>(_frame));
          std::shared_ptr<arith_expr> a2 = std::move(_f.a2);
          std::shared_ptr<arith_expr> a3 = std::move(_f.a3);
          _result = f1(*a2, std::move(_f._tmp4), *a3, std::move(_result));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_expr *_self;
      };

      /// CraneCont_BAnd: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd {
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BAnd_1: saves [a_], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd_1 {
        bool_expr a_;
      };

      /// CraneCont_BAnd_2: saves [a_], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd_2 {
        bool_expr a_;
      };

      /// CraneCont_BFalse: resumes after recursive call, then processes rest.
      struct CraneCont_BFalse {};

      /// CraneCont_BNot: saves [a_], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNot {
        bool_expr a_;
      };

      /// CraneCont_BNot_1: saves [a_], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNot_1 {
        bool_expr a_;
      };

      /// CraneCont_BNot_2: resumes after recursive call, then processes rest.
      struct CraneCont_BNot_2 {};

      /// CraneCont_BOr: saves [a_], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr {
        bool_expr a_;
      };

      /// CraneCont_BOr_1: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr_1 {
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BOr_2: saves [a_], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr_2 {
        bool_expr a_;
      };

      /// CraneCont_BTrue: resumes after recursive call, then processes rest.
      struct CraneCont_BTrue {};

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BAnd, CraneCont_BAnd_1,
                       CraneCont_BAnd_2, CraneCont_BFalse, CraneCont_BNot,
                       CraneCont_BNot_1, CraneCont_BNot_2, CraneCont_BOr,
                       CraneCont_BOr_1, CraneCont_BOr_2, CraneCont_BTrue>;
      bool_expr _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified simplify_bool: CraneEnter -> CraneCont_BAnd ->
      /// CraneCont_BAnd_1 -> CraneCont_BAnd_2 -> CraneCont_BFalse ->
      /// CraneCont_BNot -> CraneCont_BNot_1 -> CraneCont_BNot_2 ->
      /// CraneCont_BOr -> CraneCont_BOr_1 -> CraneCont_BOr_2 ->
      /// CraneCont_BTrue.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont_BAnd{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(CraneCont_BOr_1{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(CraneCont_BNot_2{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BAnd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd>(_frame));
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          bool_expr _tmp5 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp5.v_mut())) {
            _stack.emplace_back(CraneCont_BTrue{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp5.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp5.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_tmp5.v_mut());
            bool_expr a_ = bool_expr::band(*a00, *a10);
            _stack.emplace_back(CraneCont_BAnd_1{std::move(a_)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp5.v_mut())) {
            auto &[a00, a10] = std::get<typename bool_expr::BOr>(_tmp5.v_mut());
            bool_expr a_ = bool_expr::bor(*a00, *a10);
            _stack.emplace_back(CraneCont_BOr{std::move(a_)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            auto &[a00] = std::get<typename bool_expr::BNot>(_tmp5.v_mut());
            bool_expr a_ = bool_expr::bnot(*a00);
            _stack.emplace_back(CraneCont_BNot{std::move(a_)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<CraneCont_BAnd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd_1>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp2 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp2.v_mut())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp2.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp2.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp2.v_mut());
            _result =
                bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp2.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp2.v_mut());
            _result =
                bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp2.v_mut());
            _result = bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<CraneCont_BAnd_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd_2>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp7 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp7.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp7.v_mut())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp7.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp7.v_mut());
            _result =
                bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp7.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp7.v_mut());
            _result = bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp7.v_mut());
            _result = bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<CraneCont_BFalse>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BFalse>(_frame));
          bool_expr _tmp6 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp6.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp6.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp6.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp6.v_mut());
            _result = bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp6.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp6.v_mut());
            _result = bool_expr::bor(*a01, *a11);
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp6.v_mut());
            _result = bool_expr::bnot(*a01);
          }
        } else if (std::holds_alternative<CraneCont_BNot>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNot>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp4 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp4.v_mut())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp4.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp4.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp4.v_mut());
            _result =
                bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp4.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp4.v_mut());
            _result =
                bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp4.v_mut());
            _result = bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<CraneCont_BNot_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNot_1>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp9 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp9.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp9.v_mut())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp9.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp9.v_mut());
            _result =
                bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp9.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp9.v_mut());
            _result = bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp9.v_mut());
            _result = bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<CraneCont_BNot_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNot_2>(_frame));
          bool_expr _tmp11 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp11.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp11.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp11.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_tmp11.v_mut());
            _result = bool_expr::bnot(bool_expr::band(*a00, *a10));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp11.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_tmp11.v_mut());
            _result = bool_expr::bnot(bool_expr::bor(*a00, *a10));
          } else {
            auto &[a00] = std::get<typename bool_expr::BNot>(_tmp11.v_mut());
            _result = bool_expr::bnot(bool_expr::bnot(*a00));
          }
        } else if (std::holds_alternative<CraneCont_BOr>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BOr>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp3 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp3.v_mut())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp3.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp3.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp3.v_mut());
            _result =
                bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp3.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp3.v_mut());
            _result =
                bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp3.v_mut());
            _result = bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<CraneCont_BOr_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BOr_1>(_frame));
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          bool_expr _tmp10 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp10.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp10.v_mut())) {
            _stack.emplace_back(CraneCont_BFalse{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp10.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BAnd>(_tmp10.v_mut());
            bool_expr a_ = bool_expr::band(*a00, *a10);
            _stack.emplace_back(CraneCont_BAnd_2{std::move(a_)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp10.v_mut())) {
            auto &[a00, a10] =
                std::get<typename bool_expr::BOr>(_tmp10.v_mut());
            bool_expr a_ = bool_expr::bor(*a00, *a10);
            _stack.emplace_back(CraneCont_BOr_2{std::move(a_)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            auto &[a00] = std::get<typename bool_expr::BNot>(_tmp10.v_mut());
            bool_expr a_ = bool_expr::bnot(*a00);
            _stack.emplace_back(CraneCont_BNot_1{std::move(a_)});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<CraneCont_BOr_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BOr_2>(_frame));
          bool_expr a_ = std::move(_f.a_);
          bool_expr _tmp8 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp8.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp8.v_mut())) {
            _result = std::move(a_);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp8.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp8.v_mut());
            _result =
                bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp8.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp8.v_mut());
            _result = bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp8.v_mut());
            _result = bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else {
          auto _f = std::move(std::get<CraneCont_BTrue>(_frame));
          bool_expr _tmp1 = std::move(_result);
          if (std::holds_alternative<typename bool_expr::BTrue>(
                  _tmp1.v_mut())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _tmp1.v_mut())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _tmp1.v_mut())) {
            auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_tmp1.v_mut());
            _result = bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _tmp1.v_mut())) {
            auto &[a01, a11] = std::get<typename bool_expr::BOr>(_tmp1.v_mut());
            _result = bool_expr::bor(*a01, *a11);
          } else {
            auto &[a01] = std::get<typename bool_expr::BNot>(_tmp1.v_mut());
            _result = bool_expr::bnot(*a01);
          }
        }
      }
      return _result;
    }

    bool eval_bool() const {
      const bool_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_expr *_self;
      };

      /// CraneCont_BAnd: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd {
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BAnd_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd_1 {
        bool _tmp2;
      };

      /// CraneCont_BNot: resumes after recursive call, then processes rest.
      struct CraneCont_BNot {};

      /// CraneCont_BOr: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr {
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BOr_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr_1 {
        bool _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BAnd, CraneCont_BAnd_1,
                       CraneCont_BNot, CraneCont_BOr, CraneCont_BOr_1>;
      bool _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_bool: CraneEnter -> CraneCont_BAnd -> CraneCont_BAnd_1
      /// -> CraneCont_BNot -> CraneCont_BOr -> CraneCont_BOr_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont_BAnd{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(CraneCont_BOr{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(CraneCont_BNot{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BAnd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd>(_frame));
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_BAnd_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_BAnd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd_1>(_frame));
          _result = (_f._tmp2 && std::move(_result));
        } else if (std::holds_alternative<CraneCont_BNot>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNot>(_frame));
          _result = !(std::move(_result));
        } else if (std::holds_alternative<CraneCont_BOr>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BOr>(_frame));
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_BOr_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BOr_1>(_frame));
          _result = (_f._tmp4 || std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 bool_expr_rec(const T1 &f, const T1 &f0, F2 &&f1, F3 &&f2,
                     F4 &&f3) const {
      return this->template bool_expr_rect<T1>(f, f0, f1, f2, f3);
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 bool_expr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_expr *_self;
      };

      /// CraneCont_BAnd: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd {
        std::shared_ptr<bool_expr> a0;
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BAnd_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_BAnd_1 {
        T1 _tmp2;
        std::shared_ptr<bool_expr> a0;
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BNot: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNot {
        std::shared_ptr<bool_expr> a0;
      };

      /// CraneCont_BOr: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr {
        std::shared_ptr<bool_expr> a0;
        std::shared_ptr<bool_expr> a1;
      };

      /// CraneCont_BOr_1: saves [_tmp4, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_BOr_1 {
        T1 _tmp4;
        std::shared_ptr<bool_expr> a0;
        std::shared_ptr<bool_expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BAnd, CraneCont_BAnd_1,
                       CraneCont_BNot, CraneCont_BOr, CraneCont_BOr_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified bool_expr_rect: CraneEnter -> CraneCont_BAnd ->
      /// CraneCont_BAnd_1 -> CraneCont_BNot -> CraneCont_BOr ->
      /// CraneCont_BOr_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont_BAnd{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(CraneCont_BOr{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(CraneCont_BNot{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BAnd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd>(_frame));
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_BAnd_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_BAnd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd_1>(_frame));
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_BNot>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNot>(_frame));
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          _result = f3(*a0, std::move(_result));
        } else if (std::holds_alternative<CraneCont_BOr>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BOr>(_frame));
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_BOr_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BOr_1>(_frame));
          std::shared_ptr<bool_expr> a0 = std::move(_f.a0);
          std::shared_ptr<bool_expr> a1 = std::move(_f.a1);
          _result = f2(*a0, std::move(_f._tmp4), *a1, std::move(_result));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const list_expr *_self;
      };

      /// CraneCont_LAppend: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LAppend {
        std::shared_ptr<list_expr> a1;
      };

      /// CraneCont_LAppend_1: saves [_tmp3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LAppend_1 {
        uint64_t _tmp3;
      };

      /// CraneCont_LCons: resumes after recursive call, then processes rest.
      struct CraneCont_LCons {};

      using CraneFrame = std::variant<CraneEnter, CraneCont_LAppend,
                                      CraneCont_LAppend_1, CraneCont_LCons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified list_expr_size: CraneEnter -> CraneCont_LAppend ->
      /// CraneCont_LAppend_1 -> CraneCont_LCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(CraneCont_LCons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(CraneCont_LAppend{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            _result = UINT64_C(1);
          }
        } else if (std::holds_alternative<CraneCont_LAppend>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LAppend>(_frame));
          std::shared_ptr<list_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_LAppend_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_LAppend_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LAppend_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp3) + std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_LCons>(_frame));
          _result = (UINT64_C(1) + std::move(_result));
        }
      }
      return _result;
    }

    List<uint64_t> eval_list() const {
      const list_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const list_expr *_self;
      };

      /// CraneCont_LAppend: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LAppend {
        std::shared_ptr<list_expr> a1;
      };

      /// CraneCont_LAppend_1: saves [_tmp3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LAppend_1 {
        List<uint64_t> _tmp3;
      };

      /// CraneCont_LCons: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LCons {
        uint64_t a0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_LAppend,
                                      CraneCont_LAppend_1, CraneCont_LCons>;
      List<uint64_t> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_list: CraneEnter -> CraneCont_LAppend ->
      /// CraneCont_LAppend_1 -> CraneCont_LCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = List<uint64_t>::nil();
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(CraneCont_LCons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(CraneCont_LAppend{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = ListDef::template repeat<uint64_t>(a1, a0);
          }
        } else if (std::holds_alternative<CraneCont_LAppend>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LAppend>(_frame));
          std::shared_ptr<list_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_LAppend_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_LAppend_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LAppend_1>(_frame));
          _result = std::move(_f._tmp3).app(std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_LCons>(_frame));
          uint64_t a0 = _f.a0;
          _result = List<uint64_t>::cons(a0, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1, typename F2, typename F3>
    T1 list_expr_rec(const T1 &f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      return this->template list_expr_rect<T1>(f, f0, f1, f2);
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F3 &, const uint64_t &,
                                     const uint64_t &>
    T1 list_expr_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const list_expr *_self;
      };

      /// CraneCont_LAppend: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LAppend {
        std::shared_ptr<list_expr> a0;
        std::shared_ptr<list_expr> a1;
      };

      /// CraneCont_LAppend_1: saves [_tmp3, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_LAppend_1 {
        T1 _tmp3;
        std::shared_ptr<list_expr> a0;
        std::shared_ptr<list_expr> a1;
      };

      /// CraneCont_LCons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_LCons {
        uint64_t a0;
        std::shared_ptr<list_expr> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_LAppend,
                                      CraneCont_LAppend_1, CraneCont_LCons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified list_expr_rect: CraneEnter -> CraneCont_LAppend ->
      /// CraneCont_LAppend_1 -> CraneCont_LCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(CraneCont_LCons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(CraneCont_LAppend{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(a0, a1);
          }
        } else if (std::holds_alternative<CraneCont_LAppend>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LAppend>(_frame));
          std::shared_ptr<list_expr> a0 = std::move(_f.a0);
          std::shared_ptr<list_expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_LAppend_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_LAppend_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LAppend_1>(_frame));
          std::shared_ptr<list_expr> a0 = std::move(_f.a0);
          std::shared_ptr<list_expr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp3), *a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_LCons>(_frame));
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
