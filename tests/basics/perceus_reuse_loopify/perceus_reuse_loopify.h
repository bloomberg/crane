#ifndef INCLUDED_PERCEUS_REUSE_LOOPIFY
#define INCLUDED_PERCEUS_REUSE_LOOPIFY

#include "crane_fn.h"
#include "rc.h"
#include "small_vector.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct R {
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      crane::rc<lst> a1;
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
      return lst(Cons{a0, crane::make_rc<lst>(std::move(a1))});
    }

    static lst cons__reuse(crane::rc<lst> _tok, uint64_t a0, lst a1) {
      return lst(Cons{
          a0, crane::make_rc_reusing<lst>(std::move(_tok), std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      crane::small_vector<crane::rc<lst>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
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
          _drain(_cur->v_mut());
        }
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
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified lst_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = std::move(f);
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
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified lst_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = std::move(f);
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

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static lst map1(F0 &&f, lst l) {
    crane::rc<lst> _head{};
    crane::rc<lst> *_write = &_head;
    crane::rc<lst> _own = crane::rc<lst>();
    bool _uniq = true;
    const lst *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename lst::Nil>(_loop_l->v())) {
        *_write = crane::make_rc<lst>(lst::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename lst::Cons>(_loop_l->v());
        auto _rs = crane::reuse_step(_own, _uniq, a1);
        auto _cell = crane::make_rc_reusing_unchecked(
            std::move(_rs.token), typename lst::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename lst::Cons>((*_write)->v_mut()).a1;
        _own = std::move(_rs.next);
        _loop_l = _own.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  static lst rev_append1(const lst &l, lst acc);
  static lst rev1(const lst &l);
  static uint64_t sum1(const lst &l);
};

#endif // INCLUDED_PERCEUS_REUSE_LOOPIFY
