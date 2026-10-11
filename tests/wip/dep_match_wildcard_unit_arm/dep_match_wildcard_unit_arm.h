#ifndef INCLUDED_DEP_MATCH_WILDCARD_UNIT_ARM
#define INCLUDED_DEP_MATCH_WILDCARD_UNIT_ARM

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct DepMatchWildcardUnitArm {
  struct ty {
    // TYPES
    struct TNat {};

    struct TBool {};

    struct TArr {
      std::shared_ptr<ty> a0;
      std::shared_ptr<ty> a1;
    };

    using variant_t = std::variant<TNat, TBool, TArr>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TNat _v) : v_(_v) {}

    explicit ty(TBool _v) : v_(_v) {}

    explicit ty(TArr _v) : v_(std::move(_v)) {}

    static ty tnat() { return ty(TNat{}); }

    static ty tbool() { return ty(TBool{}); }

    static ty tarr(ty a0, ty a1) {
      return ty(TArr{std::make_shared<ty>(std::move(a0)),
                     std::make_shared<ty>(std::move(a1))});
    }

    // MANIPULATORS
    ~ty() {
      if (std::holds_alternative<TNat>(v_mut())) {
        return;
      }
      if (std::holds_alternative<TBool>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<TArr>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ty>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TArr>(&_v)) {
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

    ty(const ty &) = default;
    ty &operator=(const ty &) = default;
    ty(ty &&) = default;
    ty &operator=(ty &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F2> T1 ty_rec(T1 f, T1 f0, F2 &&f1) const {
      return this->template ty_rect<T1>(std::move(f), std::move(f0), f1);
    }

    template <typename T1, typename F2> T1 ty_rect(T1 f, T1 f0, F2 &&f1) const {
      const ty *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ty *_self;
      };

      /// CraneCont_TArr: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TArr {
        std::shared_ptr<ty> a0;
        const ty *a1;
      };

      /// CraneCont_TArr_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TArr_1 {
        T1 _tmp2;
        std::shared_ptr<ty> a0;
        const ty *a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_TArr, CraneCont_TArr_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ty_rect: CraneEnter -> CraneCont_TArr -> CraneCont_TArr_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ty *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ty::TNat>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename ty::TBool>(_sv.v())) {
            _result = f0;
          } else {
            const auto &[a0, a1] = std::get<typename ty::TArr>(_sv.v());
            _stack.emplace_back(CraneCont_TArr{a0, crane_raw(a1)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TArr>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TArr>(_frame));
          std::shared_ptr<ty> a0 = std::move(_f.a0);
          const ty &a1 = *_f.a1;
          _stack.emplace_back(
              CraneCont_TArr_1{std::move(_result), std::move(a0), &a1});
          _stack.emplace_back(CraneEnter{_f.a1});
        } else {
          auto _f = std::move(std::get<CraneCont_TArr_1>(_frame));
          std::shared_ptr<ty> a0 = std::move(_f.a0);
          const ty &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct exp {
    // TYPES
    struct ELit {
      uint64_t a0;
    };

    struct EB {
      bool a0;
    };

    struct EIf {
      ty t;
      std::shared_ptr<exp> a1;
    };

    using variant_t = std::variant<ELit, EB, EIf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    exp() {}

    explicit exp(ELit _v) : v_(std::move(_v)) {}

    explicit exp(EB _v) : v_(std::move(_v)) {}

    explicit exp(EIf _v) : v_(std::move(_v)) {}

    static exp elit(uint64_t a0) { return exp(ELit{a0}); }

    static exp eb(bool a0) { return exp(EB{a0}); }

    static exp eif(ty t, exp a1) {
      return exp(EIf{std::move(t), std::make_shared<exp>(std::move(a1))});
    }

    // MANIPULATORS
    ~exp() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<exp> {
        if (auto *_alt = std::get_if<EIf>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<exp> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    exp(const exp &) = default;
    exp &operator=(const exp &) = default;
    exp(exp &&) = default;
    exp &operator=(exp &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t evn() const {
      const exp *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename exp::ELit>(_sv.v())) {
          const auto &[a0] = std::get<typename exp::ELit>(_sv.v());
          return a0;
        } else if (std::holds_alternative<typename exp::EB>(_sv.v())) {
          return std::monostate{};
        } else {
          const auto &[t0, a1] = std::get<typename exp::EIf>(_sv.v());
          if (std::holds_alternative<typename ty::TNat>(t0.v())) {
            _loop_self = crane_raw(a1);
          } else {
            return std::monostate{};
          }
        }
      }
    }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 exp_rect(F0 &&f, F1 &&f0, F2 &&f1, const ty &, const exp &e) {
    if (std::holds_alternative<typename exp::ELit>(e.v())) {
      const auto &[a0] = std::get<typename exp::ELit>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename exp::EB>(e.v())) {
      const auto &[a0] = std::get<typename exp::EB>(e.v());
      return f0(a0);
    } else {
      const auto &[t0, a1] = std::get<typename exp::EIf>(e.v());
      return f1(t0, *a1, exp_rect<T1>(f, f0, f1, t0, *a1));
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
  static T1 exp_rec(F0 &&f, F1 &&f0, F2 &&f1, const ty &_x, const exp &e) {
    return exp_rect<T1>(f, f0, f1, _x, e);
  }

  static inline const uint64_t result =
      exp::eif(ty::tnat(), exp::elit(UINT64_C(4))).evn();
};

#endif // INCLUDED_DEP_MATCH_WILDCARD_UNIT_ARM
