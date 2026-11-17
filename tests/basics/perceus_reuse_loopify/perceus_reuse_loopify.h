#ifndef INCLUDED_PERCEUS_REUSE_LOOPIFY
#define INCLUDED_PERCEUS_REUSE_LOOPIFY

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "rc.h"
#include "small_vector.h"

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

    static lst cons(uint64_t a0, crane::child_slot<lst> a1) {
      return lst(Cons{a0, a1.take()});
    }

    static lst cons_crane_reuse(crane::rc<lst> _tok, uint64_t a0, lst a1) {
      return lst(
          Cons{a0,
               crane::make_rc_reusing<lst>(std::move(_tok), std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> crane::rc<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      crane::rc<lst> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) = default;
    lst &operator=(lst &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 lst_rect(T1 f, F1 &&f0, const lst &l) {
    // Explicit stack replaces the non-tail recursion of lst_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const lst *l;
    };

    struct _after_lst_rect_in_Cons {
      uint64_t a0;
      crane::rc<lst> a1;
    };

    using _frame = std::variant<_call, _after_lst_rect_in_Cons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_after_lst_rect_in_Cons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_lst_rect_in_Cons>(_popped));
        _stack.pop_back();
        uint64_t a0 = _f.a0;
        crane::rc<lst> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 lst_rec(T1 f, F1 &&f0, const lst &l) {
    return lst_rect<T1>(std::move(f), f0, l);
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
  static lst map1(F0 &&f, lst l) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills. The input's cells are reused in place while uniquely owned.
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
