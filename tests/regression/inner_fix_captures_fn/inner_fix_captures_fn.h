#ifndef INCLUDED_INNER_FIX_CAPTURES_FN
#define INCLUDED_INNER_FIX_CAPTURES_FN

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct InnerFixCapturesFn {
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rect(T1 f, F1 &&f0,
                     const lst &l) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const lst *l;
    };

    /// _Resume_Cons: saves [a1, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      lst a1;
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified lst_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{*a1, a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rec(T1 f, F1 &&f0,
                    const lst &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const lst *l;
    };

    /// _Resume_Cons: saves [a1, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      lst a1;
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified lst_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{*a1, a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t walk(crane::fn<uint64_t(uint64_t)> f,
                       const lst &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const lst *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      uint64_t _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified walk: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{[&]() {
            auto inner_impl = [&](auto &, const lst &m,
                                  uint64_t a) -> uint64_t {
              uint64_t _loop_a = std::move(a);
              const lst *_loop_m = &m;
              while (true) {
                if (std::holds_alternative<typename lst::Nil>(_loop_m->v())) {
                  return _loop_a;
                } else {
                  const auto &[a2, a3] =
                      std::get<typename lst::Cons>(_loop_m->v());
                  _loop_a = (_loop_a + f(a2));
                  _loop_m = crane_raw(a3);
                }
              }
            };
            auto inner = [&](const lst &m, uint64_t a) -> uint64_t {
              return inner_impl(inner_impl, m, a);
            };
            return inner(*a1, f(a0));
          }()});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f._s0 + std::move(_result));
      }
    }
    return _result;
  }

  static lst mk(uint64_t n);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_INNER_FIX_CAPTURES_FN
