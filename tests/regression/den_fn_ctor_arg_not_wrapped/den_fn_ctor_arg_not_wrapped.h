#ifndef INCLUDED_DEN_FN_CTOR_ARG_NOT_WRAPPED
#define INCLUDED_DEN_FN_CTOR_ARG_NOT_WRAPPED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct DenFnCtorArgNotWrapped {
  struct ty {
    // TYPES
    struct TNat {};

    struct TFun {
      std::shared_ptr<ty> a0;
      std::shared_ptr<ty> a1;
    };

    using variant_t = std::variant<TNat, TFun>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TNat _v) : v_(_v) {}

    explicit ty(TFun _v) : v_(std::move(_v)) {}

    static ty tnat() { return ty(TNat{}); }

    static ty tfun(ty a0, ty a1) {
      return ty(TFun{std::make_shared<ty>(std::move(a0)),
                     std::make_shared<ty>(std::move(a1))});
    }

    // MANIPULATORS
    ~ty() {
      if (std::holds_alternative<TNat>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<TFun>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ty>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TFun>(&_v)) {
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

    template <typename T1, typename F1> T1 ty_rec(T1 f, F1 &&f0) const {
      return this->template ty_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 ty_rect(T1 f, F1 &&f0) const {
      const ty *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ty *_self;
      };

      /// CraneCont_TFun: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TFun {
        std::shared_ptr<ty> a0;
        const ty *a1;
      };

      /// CraneCont_TFun_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TFun_1 {
        T1 _tmp2;
        std::shared_ptr<ty> a0;
        const ty *a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_TFun, CraneCont_TFun_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ty_rect: CraneEnter -> CraneCont_TFun -> CraneCont_TFun_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ty *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ty::TNat>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename ty::TFun>(_sv.v());
            _stack.emplace_back(CraneCont_TFun{a0, crane_raw(a1)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TFun>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TFun>(_frame));
          std::shared_ptr<ty> a0 = std::move(_f.a0);
          const ty &a1 = *_f.a1;
          _stack.emplace_back(
              CraneCont_TFun_1{std::move(_result), std::move(a0), &a1});
          _stack.emplace_back(CraneEnter{_f.a1});
        } else {
          auto _f = std::move(std::get<CraneCont_TFun_1>(_frame));
          std::shared_ptr<ty> a0 = std::move(_f.a0);
          const ty &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  using den = crane::obj;

  struct box {
    // DATA
    den a0;

    // ACCESSORS
    box clone() const { return {a0}; }

    // CREATORS
    static box box0(den a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, const den &>
  static T1 box_rect(const ty &, F1 &&f, const box &b) {
    const auto &[a0] = b;
    return f(a0);
  }

  template <typename T1, typename F1>
  static T1 box_rec(const ty &_x, F1 &&f, const box &b) {
    return box_rect<T1>(_x, f, b);
  }

  static den unbox(const ty &_x, const box &b);
  static inline const box fb =
      box::box0(crane_erase_fn([](uint64_t x) { return (x + 1); }));
  static inline const uint64_t result = crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(unbox(
          ty::tfun(ty::tnat(), ty::tnat()), fb))(crane::obj(UINT64_C(4))));
};

#endif // INCLUDED_DEN_FN_CTOR_ARG_NOT_WRAPPED
