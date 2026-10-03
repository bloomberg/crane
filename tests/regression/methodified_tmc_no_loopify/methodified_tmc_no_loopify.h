#ifndef INCLUDED_METHODIFIED_TMC_NO_LOOPIFY
#define INCLUDED_METHODIFIED_TMC_NO_LOOPIFY

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MethodifiedTmcNoLoopify {
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    static lst nil() { return lst(Nil{}); }

    static lst cons(uint64_t a0, lst a1) {
      return lst(Cons{a0, std::make_shared<lst>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) noexcept = default;
    lst &operator=(lst &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
    T1 lst_rec(T1 f, F1 &&f0) const {
      const lst *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst *_self;
      };

      /// _Cont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cons {
        uint64_t a0;
        std::shared_ptr<lst> a1;
      };

      using _Frame = std::variant<_Enter, _Cont_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rec: _Enter -> _Cont_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst::Cons>(_sv.v());
            _stack.emplace_back(_Cont_Cons{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_Cons>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<lst> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
    T1 lst_rect(T1 f, F1 &&f0) const {
      const lst *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst *_self;
      };

      /// _Cont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Cons {
        uint64_t a0;
        std::shared_ptr<lst> a1;
      };

      using _Frame = std::variant<_Enter, _Cont_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rect: _Enter -> _Cont_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst::Cons>(_sv.v());
            _stack.emplace_back(_Cont_Cons{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_Cons>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<lst> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct wrap {
    // TYPES
    struct W {
      lst a0;
    };

    struct WW {
      std::shared_ptr<wrap> a0;
    };

    using variant_t = std::variant<W, WW>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrap() {}

    explicit wrap(W _v) : v_(std::move(_v)) {}

    explicit wrap(WW _v) : v_(std::move(_v)) {}

    static wrap w(lst a0) { return wrap(W{std::move(a0)}); }

    static wrap ww(wrap a0) {
      return wrap(WW{std::make_shared<wrap>(std::move(a0))});
    }

    // MANIPULATORS
    ~wrap() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<wrap> {
        if (auto *_alt = std::get_if<WW>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<wrap> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    wrap(const wrap &) = default;
    wrap &operator=(const wrap &) = default;
    wrap(wrap &&) noexcept = default;
    wrap &operator=(wrap &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t wdepth() const {
      const wrap *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const wrap *_self;
      };

      /// _Resume_WW: resumes after recursive call with _result.
      struct _Resume_WW {};

      using _Frame = std::variant<_Enter, _Resume_WW>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified wdepth: _Enter -> _Resume_WW.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const wrap *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename wrap::W>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0] = std::get<typename wrap::WW>(_sv.v());
            _stack.emplace_back(_Resume_WW{});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_WW>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    wrap wraps(uint64_t n) const {
      const wrap *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const wrap *_self;
        uint64_t n;
      };

      /// _Resume_k: resumes after recursive call with _result.
      struct _Resume_k {};

      using _Frame = std::variant<_Enter, _Resume_k>;
      wrap _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, n});
      /// Loopified wraps: _Enter -> _Resume_k.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const wrap *_self = _f._self;
          uint64_t n = _f.n;
          if (n <= 0) {
            _result = std::move(*_self);
          } else {
            uint64_t k = n - 1;
            _stack.emplace_back(_Resume_k{});
            _stack.emplace_back(_Enter{crane_raw(_self), k});
          }
        } else {
          auto _f = std::move(std::get<_Resume_k>(_frame));
          _result = wrap::ww(std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, lst &> &&
               std::is_invocable_r_v<T1, F1 &, wrap &, T1 &>
    T1 wrap_rec(F0 &&f, F1 &&f0) const {
      const wrap *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const wrap *_self;
      };

      /// _Cont_WW: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct _Cont_WW {
        std::shared_ptr<wrap> a0;
      };

      using _Frame = std::variant<_Enter, _Cont_WW>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified wrap_rec: _Enter -> _Cont_WW.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const wrap *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename wrap::W>(_sv.v())) {
            const auto &[a0] = std::get<typename wrap::W>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0] = std::get<typename wrap::WW>(_sv.v());
            _stack.emplace_back(_Cont_WW{a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_WW>(_frame));
          std::shared_ptr<wrap> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, lst &> &&
               std::is_invocable_r_v<T1, F1 &, wrap &, T1 &>
    T1 wrap_rect(F0 &&f, F1 &&f0) const {
      const wrap *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const wrap *_self;
      };

      /// _Cont_WW: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct _Cont_WW {
        std::shared_ptr<wrap> a0;
      };

      using _Frame = std::variant<_Enter, _Cont_WW>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified wrap_rect: _Enter -> _Cont_WW.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const wrap *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename wrap::W>(_sv.v())) {
            const auto &[a0] = std::get<typename wrap::W>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0] = std::get<typename wrap::WW>(_sv.v());
            _stack.emplace_back(_Cont_WW{a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_WW>(_frame));
          std::shared_ptr<wrap> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t deep =
      wrap::w(lst::nil()).wraps(UINT64_C(100000)).wdepth();
};

#endif // INCLUDED_METHODIFIED_TMC_NO_LOOPIFY
