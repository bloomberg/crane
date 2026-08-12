#ifndef INCLUDED_PERCEUS_REUSE
#define INCLUDED_PERCEUS_REUSE

#include "rc.h"
#include "small_vector.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
  static T1 lst_rect(T1 f, F1 &&f0, const lst &l) {
    if (std::holds_alternative<typename lst::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
      return f0(a0, *a1, lst_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rec(T1 f, F1 &&f0, const lst &l) {
    if (std::holds_alternative<typename lst::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
      return f0(a0, *a1, lst_rec<T1>(f, f0, *a1));
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static lst map1(F0 &&f, lst l) {
    if (l.v().index() == 1) {
      if (std::get<1>(l.v_mut()).a1.use_count() == 1) {
        uint64_t x = std::move(std::get<1>(l.v_mut()).a0);
        lst xs = std::move(*std::get<1>(l.v_mut()).a1);
        return lst::cons__reuse(std::move(std::get<1>(l.v_mut()).a1), f(x),
                                map1(f, std::move(xs)));
      } else {
        if (std::holds_alternative<typename lst::Nil>(l.v_mut())) {
          return lst::nil();
        } else {
          auto &[a0, a1] = std::get<typename lst::Cons>(l.v_mut());
          return lst::cons(f(std::move(a0)), map1(f, *a1));
        }
      }
    } else {
      if (std::holds_alternative<typename lst::Nil>(l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] = std::get<typename lst::Cons>(l.v_mut());
        return lst::cons(f(std::move(a0)), map1(f, *a1));
      }
    }
  }

  static lst rev_append1(const lst &l, lst acc);
  static lst rev1(const lst &l);
  static uint64_t sum1(const lst &l);
};

#endif // INCLUDED_PERCEUS_REUSE
