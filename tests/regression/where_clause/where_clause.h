#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct WhereClause {
  struct Expr {
    // TYPES
    struct Num {
      uint64_t a0;
    };

    struct Plus {
      std::shared_ptr<Expr> a0;
      std::shared_ptr<Expr> a1;
    };

    struct Times {
      std::shared_ptr<Expr> a0;
      std::shared_ptr<Expr> a1;
    };

    using variant_t = std::variant<Num, Plus, Times>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(Num _v) : v_(std::move(_v)) {}

    explicit Expr(Plus _v) : v_(std::move(_v)) {}

    explicit Expr(Times _v) : v_(std::move(_v)) {}

    static Expr num(uint64_t a0) { return Expr(Num{a0}); }

    static Expr plus(Expr a0, Expr a1) {
      return Expr(Plus{std::make_shared<Expr>(std::move(a0)),
                       std::make_shared<Expr>(std::move(a1))});
    }

    static Expr times(Expr a0, Expr a1) {
      return Expr(Times{std::make_shared<Expr>(std::move(a0)),
                        std::make_shared<Expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~Expr() {
      if (std::holds_alternative<Num>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Plus>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Times>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<Expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Plus>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Times>(&_v)) {
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

    Expr(const Expr &) = default;
    Expr &operator=(const Expr &) = default;
    Expr(Expr &&) = default;
    Expr &operator=(Expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t expr_size() const {
      const Expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const Expr *_self;
      };

      /// CraneCont_Plus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_Times: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Times {
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Times_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Times_1 {
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Plus, CraneCont_Plus_1,
                       CraneCont_Times, CraneCont_Times_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified expr_size: CraneEnter -> CraneCont_Plus -> CraneCont_Plus_1
      /// -> CraneCont_Times -> CraneCont_Times_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(CraneCont_Times{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Plus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Plus_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
        } else if (std::holds_alternative<CraneCont_Times>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Times>(_frame));
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Times_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Times_1>(_frame));
          _result = ((UINT64_C(1) + _f._tmp4) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval() const {
      const Expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const Expr *_self;
      };

      /// CraneCont_Plus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_Times: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Times {
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Times_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Times_1 {
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Plus, CraneCont_Plus_1,
                       CraneCont_Times, CraneCont_Times_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval: CraneEnter -> CraneCont_Plus -> CraneCont_Plus_1 ->
      /// CraneCont_Times -> CraneCont_Times_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(CraneCont_Times{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Plus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Plus_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<CraneCont_Times>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Times>(_frame));
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Times_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Times_1>(_frame));
          _result = (_f._tmp4 * std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template Expr_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const Expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const Expr *_self;
      };

      /// CraneCont_Plus: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Plus {
        std::shared_ptr<Expr> a0;
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Plus_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Plus_1 {
        T1 _tmp2;
        std::shared_ptr<Expr> a0;
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Times: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Times {
        std::shared_ptr<Expr> a0;
        std::shared_ptr<Expr> a1;
      };

      /// CraneCont_Times_1: saves [_tmp4, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Times_1 {
        T1 _tmp4;
        std::shared_ptr<Expr> a0;
        std::shared_ptr<Expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Plus, CraneCont_Plus_1,
                       CraneCont_Times, CraneCont_Times_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified Expr_rect: CraneEnter -> CraneCont_Plus -> CraneCont_Plus_1
      /// -> CraneCont_Times -> CraneCont_Times_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(CraneCont_Plus{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(CraneCont_Times{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Plus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus>(_frame));
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Plus_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Plus_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Plus_1>(_frame));
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_Times>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Times>(_frame));
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Times_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Times_1>(_frame));
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          std::shared_ptr<Expr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp4), *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct BExpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<BExpr> a0;
      std::shared_ptr<BExpr> a1;
    };

    struct BOr {
      std::shared_ptr<BExpr> a0;
      std::shared_ptr<BExpr> a1;
    };

    struct BNot {
      std::shared_ptr<BExpr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    BExpr() {}

    explicit BExpr(BTrue _v) : v_(_v) {}

    explicit BExpr(BFalse _v) : v_(_v) {}

    explicit BExpr(BAnd _v) : v_(std::move(_v)) {}

    explicit BExpr(BOr _v) : v_(std::move(_v)) {}

    explicit BExpr(BNot _v) : v_(std::move(_v)) {}

    static BExpr btrue() { return BExpr(BTrue{}); }

    static BExpr bfalse() { return BExpr(BFalse{}); }

    static BExpr band(BExpr a0, BExpr a1) {
      return BExpr(BAnd{std::make_shared<BExpr>(std::move(a0)),
                        std::make_shared<BExpr>(std::move(a1))});
    }

    static BExpr bor(BExpr a0, BExpr a1) {
      return BExpr(BOr{std::make_shared<BExpr>(std::move(a0)),
                       std::make_shared<BExpr>(std::move(a1))});
    }

    static BExpr bnot(BExpr a0) {
      return BExpr(BNot{std::make_shared<BExpr>(std::move(a0))});
    }

    // MANIPULATORS
    ~BExpr() {
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
      crane::small_vector<std::shared_ptr<BExpr>> _stack = {};
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

    BExpr(const BExpr &) = default;
    BExpr &operator=(const BExpr &) = default;
    BExpr(BExpr &&) = default;
    BExpr &operator=(BExpr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool beval() const {
      const BExpr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const BExpr *_self;
      };

      /// CraneCont_BAnd: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd {
        std::shared_ptr<BExpr> a1;
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
        std::shared_ptr<BExpr> a1;
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
      /// Loopified beval: CraneEnter -> CraneCont_BAnd -> CraneCont_BAnd_1 ->
      /// CraneCont_BNot -> CraneCont_BOr -> CraneCont_BOr_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = true;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(CraneCont_BAnd{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(CraneCont_BOr{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(CraneCont_BNot{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BAnd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd>(_frame));
          std::shared_ptr<BExpr> a1 = std::move(_f.a1);
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
          std::shared_ptr<BExpr> a1 = std::move(_f.a1);
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
    T1 BExpr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      return this->template BExpr_rect<T1>(std::move(f), std::move(f0), f1, f2,
                                           f3);
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 BExpr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const BExpr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const BExpr *_self;
      };

      /// CraneCont_BAnd: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BAnd {
        std::shared_ptr<BExpr> a0;
        std::shared_ptr<BExpr> a1;
      };

      /// CraneCont_BAnd_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_BAnd_1 {
        T1 _tmp2;
        std::shared_ptr<BExpr> a0;
        std::shared_ptr<BExpr> a1;
      };

      /// CraneCont_BNot: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNot {
        std::shared_ptr<BExpr> a0;
      };

      /// CraneCont_BOr: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BOr {
        std::shared_ptr<BExpr> a0;
        std::shared_ptr<BExpr> a1;
      };

      /// CraneCont_BOr_1: saves [_tmp4, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_BOr_1 {
        T1 _tmp4;
        std::shared_ptr<BExpr> a0;
        std::shared_ptr<BExpr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BAnd, CraneCont_BAnd_1,
                       CraneCont_BNot, CraneCont_BOr, CraneCont_BOr_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified BExpr_rect: CraneEnter -> CraneCont_BAnd -> CraneCont_BAnd_1
      /// -> CraneCont_BNot -> CraneCont_BOr -> CraneCont_BOr_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(CraneCont_BAnd{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(CraneCont_BOr{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(CraneCont_BNot{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BAnd>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd>(_frame));
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          std::shared_ptr<BExpr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_BAnd_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_BAnd_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BAnd_1>(_frame));
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          std::shared_ptr<BExpr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_BNot>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNot>(_frame));
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          _result = f3(*a0, std::move(_result));
        } else if (std::holds_alternative<CraneCont_BOr>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BOr>(_frame));
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          std::shared_ptr<BExpr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_BOr_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BOr_1>(_frame));
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          std::shared_ptr<BExpr> a1 = std::move(_f.a1);
          _result = f2(*a0, std::move(_f._tmp4), *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct AExpr {
    // TYPES
    struct ANum {
      uint64_t a0;
    };

    struct APlus {
      std::shared_ptr<AExpr> a0;
      std::shared_ptr<AExpr> a1;
    };

    struct AIf {
      BExpr a0;
      std::shared_ptr<AExpr> a1;
      std::shared_ptr<AExpr> a2;
    };

    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    AExpr() {}

    explicit AExpr(ANum _v) : v_(std::move(_v)) {}

    explicit AExpr(APlus _v) : v_(std::move(_v)) {}

    explicit AExpr(AIf _v) : v_(std::move(_v)) {}

    static AExpr anum(uint64_t a0) { return AExpr(ANum{a0}); }

    static AExpr aplus(AExpr a0, AExpr a1) {
      return AExpr(APlus{std::make_shared<AExpr>(std::move(a0)),
                         std::make_shared<AExpr>(std::move(a1))});
    }

    static AExpr aif(BExpr a0, AExpr a1, AExpr a2) {
      return AExpr(AIf{std::move(a0), std::make_shared<AExpr>(std::move(a1)),
                       std::make_shared<AExpr>(std::move(a2))});
    }

    // MANIPULATORS
    ~AExpr() {
      if (std::holds_alternative<ANum>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<APlus>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<AIf>(&v_mut())) {
        if (!((_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<AExpr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<APlus>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<AIf>(&_v)) {
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

    AExpr(const AExpr &) = default;
    AExpr &operator=(const AExpr &) = default;
    AExpr(AExpr &&) = default;
    AExpr &operator=(AExpr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t aeval() const {
      const AExpr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const AExpr *_self;
      };

      /// CraneCont_APlus: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_APlus {
        std::shared_ptr<AExpr> a1;
      };

      /// CraneCont_APlus_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_APlus_1 {
        uint64_t _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_APlus, CraneCont_APlus_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified aeval: CraneEnter -> CraneCont_APlus -> CraneCont_APlus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(CraneCont_APlus{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename AExpr::AIf>(_sv.v());
            if (a0.beval()) {
              _stack.emplace_back(CraneEnter{crane_raw(a1)});
            } else {
              _stack.emplace_back(CraneEnter{crane_raw(a2)});
            }
          }
        } else if (std::holds_alternative<CraneCont_APlus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_APlus>(_frame));
          std::shared_ptr<AExpr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_APlus_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_APlus_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template AExpr_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const AExpr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const AExpr *_self;
      };

      /// CraneCont_AIf: saves [a2, a3, a4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_AIf {
        BExpr a2;
        std::shared_ptr<AExpr> a3;
        std::shared_ptr<AExpr> a4;
      };

      /// CraneCont_AIf_1: saves [_tmp4, a2, a3, a4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_AIf_1 {
        T1 _tmp4;
        BExpr a2;
        std::shared_ptr<AExpr> a3;
        std::shared_ptr<AExpr> a4;
      };

      /// CraneCont_APlus: saves [a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_APlus {
        std::shared_ptr<AExpr> a2;
        std::shared_ptr<AExpr> a3;
      };

      /// CraneCont_APlus_1: saves [_tmp2, a2, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_APlus_1 {
        T1 _tmp2;
        std::shared_ptr<AExpr> a2;
        std::shared_ptr<AExpr> a3;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_AIf, CraneCont_AIf_1,
                       CraneCont_APlus, CraneCont_APlus_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified AExpr_rect: CraneEnter -> CraneCont_AIf -> CraneCont_AIf_1
      /// -> CraneCont_APlus -> CraneCont_APlus_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a2, a3] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(CraneCont_APlus{a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          } else {
            const auto &[a2, a3, a4] = std::get<typename AExpr::AIf>(_sv.v());
            _stack.emplace_back(CraneCont_AIf{a2, a3, a4});
            _stack.emplace_back(CraneEnter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<CraneCont_AIf>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AIf>(_frame));
          BExpr a2 = std::move(_f.a2);
          std::shared_ptr<AExpr> a3 = std::move(_f.a3);
          std::shared_ptr<AExpr> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_AIf_1{std::move(_result), std::move(a2),
                                              std::move(a3), a4});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else if (std::holds_alternative<CraneCont_AIf_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_AIf_1>(_frame));
          BExpr a2 = std::move(_f.a2);
          std::shared_ptr<AExpr> a3 = std::move(_f.a3);
          std::shared_ptr<AExpr> a4 = std::move(_f.a4);
          _result = f1(a2, *a3, std::move(_f._tmp4), *a4, std::move(_result));
        } else if (std::holds_alternative<CraneCont_APlus>(_frame)) {
          auto _f = std::move(std::get<CraneCont_APlus>(_frame));
          std::shared_ptr<AExpr> a2 = std::move(_f.a2);
          std::shared_ptr<AExpr> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_APlus_1{std::move(_result), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_APlus_1>(_frame));
          std::shared_ptr<AExpr> a2 = std::move(_f.a2);
          std::shared_ptr<AExpr> a3 = std::move(_f.a3);
          _result = f0(*a2, std::move(_f._tmp2), *a3, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t test_eval_plus =
      Expr::plus(Expr::num(UINT64_C(3)), Expr::num(UINT64_C(4))).eval();
  static inline const uint64_t test_eval_times =
      Expr::times(Expr::num(UINT64_C(5)), Expr::num(UINT64_C(6))).eval();
  static inline const uint64_t test_eval_nested =
      Expr::plus(Expr::times(Expr::num(UINT64_C(2)), Expr::num(UINT64_C(3))),
                 Expr::num(UINT64_C(1)))
          .eval();
  static inline const uint64_t test_size =
      Expr::plus(Expr::times(Expr::num(UINT64_C(2)), Expr::num(UINT64_C(3))),
                 Expr::num(UINT64_C(1)))
          .expr_size();
  static inline const bool test_beval =
      BExpr::band(BExpr::btrue(), BExpr::bnot(BExpr::bfalse())).beval();
  static inline const uint64_t test_aeval =
      AExpr::aif(BExpr::band(BExpr::btrue(), BExpr::btrue()),
                 AExpr::anum(UINT64_C(10)), AExpr::anum(UINT64_C(20)))
          .aeval();
};

#endif // INCLUDED_WHERE_CLAUSE
